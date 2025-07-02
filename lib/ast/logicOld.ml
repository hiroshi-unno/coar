open Core
open Common.Ext
open Common.Util
open Common.Combinator

(** First-Order Fixpoint Logic with Theories *)

module Priority = struct
  type t = int

  let lowest = 0
  let let_forall_exists = lowest + 2
  let seq = let_forall_exists + 2
  let ite = seq + 2
  let assign = ite + 2
  let comma = assign + 2
  let imply_iff_xor = comma + 2
  let binary_or = imply_iff_xor + 2
  let binary_and = binary_or + 2
  let eq_neq_lt_leq_gt_geq = binary_and + 2
  let append_power = eq_neq_lt_leq_gt_geq + 2
  let cons = append_power + 2
  let add_sub = cons + 2
  let mul_div_mod = add_sub + 2
  let neg_deref = mul_div_mod + 2
  let fun_app = neg_deref + 2
  let bracket = fun_app + 2
  let highest = bracket + 2

  let add_paren outer_priority inner_priority inner_str =
    if outer_priority > inner_priority then String.paren inner_str
    else inner_str
end

module Sort = struct
  type t = ..
  and e = ..
  and o = ..

  type c = { op_sig : o; val_type : t; cont_eff : e }
  type t += SVar of Ident.svar | SArrow of t * c | SPoly of Ident.svar_set * t
  type e += EVar of Ident.evar | Pure | Eff of c * c

  type o +=
    | OpSig of
        (string, t) ALMap.t
        * Ident.rvar option (* Some r: open / None: closed *)

  (** Construction *)
  let empty_closed_opsig = OpSig (ALMap.empty, None)

  let mk_empty_open_opsig_from_rvar rv = OpSig (ALMap.empty, Some rv)

  let mk_fresh_empty_open_opsig () =
    OpSig (ALMap.empty, Some (Ident.mk_fresh_rvar ()))

  let mk_cont_eff c1 c2 = Eff (c1, c2)
  let mk_fresh_evar () = EVar (Ident.mk_fresh_evar ())
  let mk_fresh_svar () = SVar (Ident.mk_fresh_svar ())

  let mk_fresh_triple_from_sort sort =
    {
      op_sig = mk_fresh_empty_open_opsig ();
      val_type = sort;
      cont_eff = mk_fresh_evar ();
    }

  let mk_fresh_triple () = mk_fresh_triple_from_sort @@ mk_fresh_svar ()

  let mk_fresh_pure_triple_from_sort sort =
    { op_sig = mk_fresh_empty_open_opsig (); val_type = sort; cont_eff = Pure }

  let mk_fresh_pure_triple () =
    mk_fresh_pure_triple_from_sort @@ mk_fresh_svar ()

  let mk_triple_from_sort sort =
    { op_sig = empty_closed_opsig; val_type = sort; cont_eff = Pure }

  let mk_arrow ?(opsig = empty_closed_opsig) ?(cont = Pure) s1 s2 =
    SArrow (s1, { op_sig = opsig; val_type = s2; cont_eff = cont })

  let rec mk_eff_fun ?(opsig = empty_closed_opsig) ?(opsigs = None)
      ?(cont = Pure) ?(conts = None) sargs sret =
    match sargs with
    | [] -> sret
    | s :: ss ->
        {
          op_sig = opsig;
          val_type =
            SArrow
              ( s,
                match (opsigs, conts) with
                | Some (o :: os), Some (c :: cs) ->
                    mk_eff_fun ~opsig:o ~opsigs:(Some os) ~cont:c
                      ~conts:(Some cs) ss sret
                | Some (o :: os), None ->
                    mk_eff_fun ~opsig:o ~opsigs:(Some os) ss sret
                | None, Some (c :: cs) ->
                    mk_eff_fun ~cont:c ~conts:(Some cs) ss sret
                | _ -> mk_eff_fun ss sret );
          cont_eff = cont;
        }

  let rec mk_fun = function
    | [ s ] -> s
    | s :: ss -> mk_arrow s (mk_fun ss)
    | _ -> assert false

  let rec of_args_ret_pure args ret =
    match args with
    | [] -> ret
    | hd :: tl ->
        SArrow (hd, mk_fresh_pure_triple_from_sort @@ of_args_ret_pure tl ret)

  let rec of_args_ret ?opsig sargs sret =
    match sargs with
    | [] -> ([], [], sret)
    | sarg :: sargs' ->
        let evar = mk_fresh_evar () in
        let ovar =
          match opsig with
          | Some opsig -> opsig
          | None -> mk_fresh_empty_open_opsig ()
        in
        let ovars, evars, sret' = of_args_ret ?opsig sargs' sret in
        ( ovar :: ovars,
          evar :: evars,
          SArrow (sarg, { op_sig = ovar; val_type = sret'; cont_eff = evar }) )

  let mk_poly svs s = if Set.is_empty svs then s else SPoly (svs, s)

  (** Observation *)
  let is_open_opsig = function OpSig (_, Some _) -> true | _ -> false

  let is_closed_opsig = function OpSig (_, None) -> true | _ -> false

  let is_empty_opsig = function
    | OpSig (map, _) -> ALMap.is_empty map
    | _ -> false

  let is_empty_open_opsig = function
    | OpSig (map, Some _) -> ALMap.is_empty map
    | _ -> false

  let is_empty_closed_opsig = function
    | OpSig (map, None) -> ALMap.is_empty map
    | _ -> false

  let is_pure = function Pure -> true | _ -> false
  let is_eff = function Eff _ -> true | _ -> false
  let is_evar = function EVar _ -> true | _ -> false
  let is_svar = function SVar _ -> true | _ -> false
  let is_arrow = function SArrow _ -> true | _ -> false
  let is_poly = function SPoly _ -> true | _ -> false
  let is_pure_triple c = is_pure c.cont_eff && is_empty_opsig c.op_sig
  let let_eff = function Eff (c1, c2) -> (c1, c2) | _ -> assert false
  let let_evar = function EVar ev -> ev | _ -> assert false

  let rec arity_of = function
    | SArrow (_, c) -> 1 + arity_of c.val_type
    | _ -> 0 (* assert false*)

  let rec ret_of = function SArrow (_, c) -> ret_of c.val_type | sort -> sort

  let rec ret_of_comp c =
    match c.val_type with SArrow (_, c) -> ret_of_comp c | _ -> c

  let rec args_of = function
    | SArrow (s, c) -> s :: args_of c.val_type
    | _ -> []

  let rec args_ret_of = function
    | SArrow (s, c) ->
        let args, ret = args_ret_of c.val_type in
        (s :: args, ret)
    | s -> ([], s)

  let rec args_ret_of_comp c =
    match c.val_type with
    | SArrow (s, c) ->
        let args, ret = args_ret_of_comp c in
        (s :: args, ret)
    | _ -> ([], c)

  let rec mono_type_of = function SPoly (_, s) -> mono_type_of s | s -> s

  let rec poly_env_of = function
    | SPoly (svs, s) -> Set.union svs (poly_env_of s)
    | _ -> Set.Poly.empty

  let rec pure_sort_of = function
    | SVar svar -> SVar svar
    | SArrow (s, c) -> mk_arrow (pure_sort_of s) (pure_sort_of c.val_type)
    | SPoly (svs, s) -> mk_poly svs (pure_sort_of s)
    | s -> s

  let rec num_conts = function
    | EVar _ | Pure -> 0
    | Eff (_, c) -> 1 + num_conts c.cont_eff
    | _ -> failwith "num_conts"
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
  String.concat_map_set ~sep:", " penv ~f:(fun (pvar, sorts) ->
      sprintf "(%s:%s)" (Ident.name_of_pvar pvar)
      @@ String.concat_map_list ~sep:" -> " ~f:str_of_sort sorts)

type sort_subst = (Ident.svar, Sort.t) Map.Poly.t
type eff_subst = (Ident.evar, Sort.e) Map.Poly.t
type opsig_subst = (Ident.rvar, Sort.o) Map.Poly.t

let str_of_sort_env_list str_of_sort senv =
  String.concat_map_list ~sep:" " senv ~f:(fun (tvar, sort) ->
      sprintf "(%s:%s)" (Ident.name_of_tvar tvar) (str_of_sort sort))

let str_of_sort_env_map str_of_sort senv =
  String.concat_map_list ~sep:" " (Map.Poly.to_alist senv)
    ~f:(fun (tvar, sort) ->
      sprintf "(%s:%s)" (Ident.name_of_tvar tvar) (str_of_sort sort))

let str_of_sort_subst str_of_sort sub =
  String.concat_map_list ~sep:", " (Map.Poly.to_alist sub)
    ~f:(fun (svar, sort) ->
      String.paren
      @@ sprintf "%s |-> %s" (Ident.name_of_svar svar) (str_of_sort sort))

let update_sort_subst subst_sorts_sort smap svar sort =
  Map.Poly.add_exn ~key:svar ~data:sort
    (Map.Poly.map smap ~f:(subst_sorts_sort (Map.Poly.singleton svar sort)))

let mk_fresh_sort_env_list =
  List.map ~f:(fun sort -> (Ident.mk_fresh_tvar (), sort))

let mk_fresh_sort_env_list_norm next = List.map ~f:(fun sort -> (next (), sort))

(* val sort_env_list_of_sorts: ?pre:string -> Sort.t list -> sort_env_list *)
let sort_env_list_of_sorts ?(pre = "") sorts =
  let param_ident_count = ref 0 in
  let mk_param_ident () =
    incr param_ident_count;
    Ident.Tvar (pre ^ "x" ^ string_of_int !param_ident_count)
  in
  List.map sorts ~f:(fun sort -> (mk_param_ident (), sort))

(* val ren_of_sort_env_list : sort_env_list -> sort_env_list -> Ident.tvar_map *)
let ren_of_sort_env_list senv1 senv2 =
  Map.Poly.of_alist_exn
  @@ List.map2_exn senv1 senv2 ~f:(fun (x1, _) (x2, _) -> (x1, x2))

(*val refresh_sort_env_list : sort_env_list -> sort_env_list * Ident.tvar_map*)
let refresh_sort_env_list senv =
  let senv' = mk_fresh_sort_env_list @@ List.map ~f:snd senv in
  let rename = ren_of_sort_env_list senv senv' in
  (senv', rename)

let refresh_sort_env_list_norm next senv =
  let senv' = mk_fresh_sort_env_list_norm next @@ List.map ~f:snd senv in
  let rename = ren_of_sort_env_list senv senv' in
  (senv', rename)

(*val normalize_sort_env_list : sort_env_list -> sort_env_list * Ident.tvar_map*)
let normalize_sort_env_list senv =
  let senv' = sort_env_list_of_sorts @@ List.map ~f:snd senv in
  let rename = ren_of_sort_env_list senv senv' in
  (senv', rename)

type info = ..
type info += Dummy
type fun_sym = ..
type fun_sym += FunCall of string | FVar of Ident.tvar * Sort.t list * Sort.t
type pred_sym = ..

let defined_fvars : Ident.tvar Hash_set.Poly.t = Hash_set.Poly.create ()

module Type = struct
  module type TermType = sig
    type atom
    type formula
    type termSubst
    type predSubst
    type funcSubst
    type dtenv

    type t =
      | Var of Ident.tvar * Sort.t * info
      | FunApp of fun_sym * t list * info
      | LetTerm of Ident.tvar * Sort.t * t * t * info

    (** Sorts *)

    val pred_to_sort_bind : pred_bind -> sort_bind
    val pred_to_sort_env : pred_sort_env_set -> sort_env_set
    val pred_to_sort_env_map : pred_sort_env_map -> sort_env_map
    val is_bool_sort : Sort.t -> bool
    val is_int_sort : Sort.t -> bool
    val is_int_ref_sort : Sort.t -> bool
    val is_real_sort : Sort.t -> bool
    val is_bv_sort : Sort.t -> bool
    val is_ir_sort : Sort.t -> bool
    val is_irb_sort : Sort.t -> bool
    val is_dt_sort : Sort.t -> bool
    val is_array_sort : Sort.t -> bool
    val is_string_sort : Sort.t -> bool
    val is_regex_sort : Sort.t -> bool
    val occurs : Ident.svar -> Sort.t -> bool
    val occurs_cont : Ident.svar -> Sort.e -> bool
    val occurs_opsig : Ident.svar -> Sort.o -> bool
    val str_of_triple : Sort.c -> string
    val str_of_sort : Sort.t -> string
    val str_of_cont : Sort.e -> string
    val str_of_opsig : Sort.o -> string
    val short_name_of_sort : Sort.t -> string
    val sorts_of_sort : Sort.t -> Sort.t Set.Poly.t
    val svs_of_cont : Sort.e -> Ident.svar_set
    val svs_of_sort : Sort.t -> Ident.svar_set
    val svs_of_opsig : Sort.o -> Ident.svar_set
    val svs_of_triple : Sort.c -> Ident.svar_set
    val polar_svs_of_cont : pos:bool -> Sort.e -> Ident.svar_set
    val polar_svs_of_sort : pos:bool -> Sort.t -> Ident.svar_set
    val polar_svs_of_opsig : pos:bool -> Sort.o -> Ident.svar_set
    val polar_svs_of_triple : pos:bool -> Sort.c -> Ident.svar_set
    val evs_of_cont : Sort.e -> Ident.evar_set
    val evs_of_sort : Sort.t -> Ident.evar_set
    val evs_of_opsig : Sort.o -> Ident.evar_set
    val evs_of_triple : Sort.c -> Ident.evar_set
    val polar_evs_of_cont : pos:bool -> Sort.e -> Ident.evar_set
    val polar_evs_of_sort : pos:bool -> Sort.t -> Ident.evar_set
    val polar_evs_of_opsig : pos:bool -> Sort.o -> Ident.evar_set
    val polar_evs_of_triple : pos:bool -> Sort.c -> Ident.evar_set
    val rvs_of_cont : Sort.e -> Ident.rvar_set
    val rvs_of_sort : Sort.t -> Ident.rvar_set
    val rvs_of_opsig : Sort.o -> Ident.rvar_set
    val rvs_of_triple : Sort.c -> Ident.rvar_set
    val polar_rvs_of_cont : pos:bool -> Sort.e -> Ident.rvar_set
    val polar_rvs_of_sort : pos:bool -> Sort.t -> Ident.rvar_set
    val polar_rvs_of_opsig : pos:bool -> Sort.o -> Ident.rvar_set
    val polar_rvs_of_triple : pos:bool -> Sort.c -> Ident.rvar_set
    val subst_sorts_sort : sort_subst -> Sort.t -> Sort.t
    val subst_sorts_cont : sort_subst -> Sort.e -> Sort.e
    val subst_sorts_opsig : sort_subst -> Sort.o -> Sort.o
    val subst_sorts_triple : sort_subst -> Sort.c -> Sort.c
    val subst_conts_sort : eff_subst -> Sort.t -> Sort.t
    val subst_conts_cont : eff_subst -> Sort.e -> Sort.e
    val subst_conts_opsig : eff_subst -> Sort.o -> Sort.o
    val subst_opsigs_sort : opsig_subst -> Sort.t -> Sort.t
    val subst_opsigs_cont : opsig_subst -> Sort.e -> Sort.e
    val subst_opsigs_opsig : opsig_subst -> Sort.o -> Sort.o
    val subst_sort : opsig_subst * sort_subst * eff_subst -> Sort.t -> Sort.t
    val subst_cont : opsig_subst * sort_subst * eff_subst -> Sort.e -> Sort.e
    val subst_opsig : opsig_subst * sort_subst * eff_subst -> Sort.o -> Sort.o
    val subst_triple : opsig_subst * sort_subst * eff_subst -> Sort.c -> Sort.c
    val subst_all : opsig_subst * sort_subst * eff_subst -> t -> t
    val fresh_conts_sort : Sort.t -> Sort.t
    val fresh_rvs_sort : Sort.t -> Sort.t
    val fresh_rvs_cont : Sort.e -> Sort.e
    val fresh_rvs_opsig : Sort.o -> Sort.o

    val pat_match_sort :
      Sort.t -> Sort.t -> opsig_subst * sort_subst * eff_subst

    val pat_match_cont :
      Sort.e -> Sort.e -> opsig_subst * sort_subst * eff_subst

    val pat_match_opsig :
      Sort.o -> Sort.o -> opsig_subst * sort_subst * eff_subst

    (** Construction *)

    val mk_var : ?info:info -> Ident.tvar -> Sort.t -> t
    val mk_fresh_var : Sort.t -> t
    val mk_fsym_app : ?info:info -> fun_sym -> t list -> t

    val mk_fvar_app :
      ?info:info -> Ident.tvar -> Sort.t list -> Sort.t -> t list -> t

    val fvar_app_of_senv :
      ?info:info -> Ident.tvar -> sort_env_list -> Sort.t -> t

    val mk_let_term : ?info:info -> Ident.tvar -> Sort.t -> t -> t -> t
    val mk_dummy : Sort.t -> t
    val of_value : dtenv -> Value.t -> t
    val of_sort_env : sort_env_list -> t list

    (** Destruction *)

    val let_var : t -> sort_bind * info
    val let_app : t -> fun_sym * t list * info
    val let_fvar_app : t -> Ident.tvar * Sort.t list * Sort.t * t list * info
    val let_funcall : t -> string * t list * info
    val let_let_term : t -> Ident.tvar * Sort.t * t * t * info

    (** Function Symbols *)

    val is_fvar_sym : fun_sym -> bool
    val str_of_funsym : fun_sym -> string
    val rename_fun_sym : Ident.tvar_map -> fun_sym -> fun_sym
    val subst_fun_sym : (t -> string) -> termSubst -> fun_sym -> fun_sym
    val subst_sorts_fun_sym : sort_subst -> fun_sym -> fun_sym
    val subst_conts_fun_sym : eff_subst -> fun_sym -> fun_sym
    val subst_opsigs_fun_sym : opsig_subst -> fun_sym -> fun_sym
    val negate_fsym : fun_sym -> fun_sym

    (** Morphism *)

    val fold :
      f:
        < fvar : Ident.tvar -> Sort.t -> 'a
        ; fapp : fun_sym -> 'a list -> 'a
        ; flet : Ident.tvar -> Sort.t -> 'a -> 'a -> 'a > ->
      t ->
      'a

    val map_term : bool -> f:(t -> t) -> t -> t
    val iter_term : f:(t -> unit) -> t -> unit
    val map_atom : f:(atom -> formula) -> t -> t
    val map_atom_polarity : f:(bool -> atom -> formula) -> t -> bool -> t
    val iter_atom : f:(atom -> unit) -> t -> unit

    (** Printing *)

    val str_of : ?priority:Priority.t -> t -> string

    (** Observation *)

    val is_var : t -> bool
    val is_app : t -> bool
    val is_fvar_app : t -> bool
    val is_funcall : t -> bool
    val is_let_term : t -> bool
    val is_compound : t -> bool
    val is_pathexp : t -> bool
    val is_uninterpreted_term : t -> bool
    val is_let_free : t -> bool
    val is_quantifier_free : t -> bool
    val tvs_of : t -> Ident.tvar_set
    val pvs_of : t -> Ident.pvar_set
    val fvs_of : t -> Ident.tvar_set
    val svs_of : t -> Ident.svar_set
    val term_sort_env_of : ?bvs:Ident.tvar_set -> t -> sort_env_set
    val pred_sort_env_of : ?bpvs:Ident.pvar_set -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:Ident.pvar_set -> t -> sort_env_set
    val value_of : t -> Value.t
    val funsyms_of : t -> fun_sym Set.Poly.t
    val predsyms_of : t -> pred_sym Set.Poly.t
    val fvar_apps_of : t -> t Set.Poly.t
    val number_of_quantifiers : t -> int
    val pathexps_of : ?bvs:Ident.tvar_set -> t -> t Set.Poly.t
    val filtered_terms_of : f:(t -> bool) -> t -> t Set.Poly.t
    val atoms_of : ?pos:bool -> t -> atom Set.Poly.t * atom Set.Poly.t
    val body_of_let : t -> t

    val number_of_pvar_apps :
      ?ex:(Ident.tvar, int) Map.Poly.t -> bool -> t -> int

    val ast_size : t -> int

    val occur_times :
      ?map:(Ident.tvar, int) Map.Poly.t -> Ident.tvar -> t -> int

    val sort_of : t -> Sort.t
    val div_rem_of : t -> (t * t) Set.Poly.t

    (** Substitution *)

    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t

    val rename_sorted_pvars :
      (string * Sort.t list, Ident.pvar) Map.Poly.t -> t -> t

    val alpha_rename_let : ?map:Ident.tvar_map -> t -> t
    val replace_let_formula_body : formula -> t -> t
    val replace_let_body : t -> t -> t
    val subst : termSubst -> t -> t
    val subst_preds : predSubst -> t -> t
    val subst_funcs : funcSubst -> t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val aconv_tvar : t -> t
    val aconv_tvar_norm : (unit -> Ident.tvar) -> t -> t
    val aconv_pvar : t -> t

    (** Observation *)

    val let_env_of : ?map:termSubst -> t -> termSubst
    val let_sort_env_of : ?map:sort_env_map -> t -> sort_env_map

    (** Construction *)

    val insert_let_term : Ident.tvar -> Sort.t -> t -> info -> t -> t

    (** Transformation *)

    val elim_neq : t -> t
    val elim_ite : t -> (formula * t) list
    val elim_pvars : Ident.tvar_set -> t -> t
    val elim_let_with_unknowns : ?map:termSubst -> Ident.tvar_set -> t -> t
    val elim_let : ?map:termSubst -> t -> t
    val instantiate_div0_mod0 : t -> t
    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t
    val replace_div_mod : (t * t, Ident.tvar * Ident.tvar) Map.Poly.t -> t -> t
    val complete_psort : pred_sort_env_map -> t -> t
    val complete_tsort : termSubst -> t -> t

    (** Unification and Pattern Matching *)

    val unify : Ident.tvar_set -> t -> t -> termSubst option
    val pattern_match : Ident.tvar_set -> t -> t -> termSubst option
  end

  module type PredicateType = sig
    type fixpoint = Mu | Nu | Fix
    type formula
    type formula_def
    type term
    type t = Var of pred_bind | Psym of pred_sym | Fixpoint of formula_def

    (** Construction *)

    val mk_var : Ident.pvar -> Sort.t list -> t
    val mk_psym : pred_sym -> t
    val mk_fix : fixpoint -> Ident.pvar -> sort_env_list -> formula -> t

    (** Destruction *)

    val let_var : t -> pred_bind
    val let_psym : t -> pred_sym
    val let_fix : t -> formula_def

    (** Fixpoint Operators *)

    val str_of_fop : fixpoint -> string
    val flip_fop : fixpoint -> fixpoint

    (** Predicate Symbols *)

    val is_flippable_psym : pred_sym -> bool
    val is_negatable_psym : pred_sym -> bool
    val is_included_psym : pred_sym -> pred_sym -> bool
    val flip_psym : pred_sym -> pred_sym
    val negate_psym : pred_sym -> pred_sym
    val str_of_psym : pred_sym -> string

    (** Printing *)

    val str_of : t -> string

    (** Observation *)

    val is_var : t -> bool
    val is_psym : t -> bool
    val is_fix : t -> bool
    val is_infix_psym : pred_sym -> bool
    val tvs_of : t -> Ident.tvar_set
    val pvs_of : t -> Ident.pvar_set
    val fvs_of : t -> Ident.tvar_set
    val svs_of : t -> Ident.svar_set
    val term_sort_env_of : ?bvs:Ident.tvar_set -> t -> sort_env_set
    val pred_sort_env_of : ?bpvs:Ident.pvar_set -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:Ident.pvar_set -> t -> sort_env_set
    val terms_of : t -> term Set.Poly.t
    val fvar_apps_of : t -> term Set.Poly.t
    val nesting_level : t -> int
    val number_of_quantifiers : t -> int
    val funsyms_of : t -> fun_sym Set.Poly.t
    val predsyms_of : t -> pred_sym Set.Poly.t

    (** Substitution *)

    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t

    val rename_sorted_pvars :
      (string * Sort.t list, Ident.pvar) Map.Poly.t -> t -> t

    val subst_neg : Ident.pvar -> t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val aconv_tvar : t -> t
    val aconv_tvar_norm : (unit -> Ident.tvar) -> t -> t
    val aconv_pvar : t -> t

    (** Transformation *)

    val negate : ?negate_formula:(formula -> formula) -> t -> t option
    val complete_psort : pred_sort_env_map -> t -> t
    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t
  end

  module type AtomType = sig
    type predicate
    type term
    type termSubst
    type predSubst
    type funcSubst
    type formula

    type t =
      | True of info
      | False of info
      | App of predicate * term list * info

    (** Construction *)

    val mk_true : ?info:info -> unit -> t
    val mk_false : ?info:info -> unit -> t
    val mk_bool : bool -> t
    val mk_app : ?info:info -> predicate -> term list -> t
    val mk_psym_app : ?info:info -> pred_sym -> term list -> t
    val mk_pvar_app : ?info:info -> Ident.pvar -> Sort.t list -> term list -> t
    val pvar_app_of_senv : ?info:info -> Ident.pvar -> sort_env_list -> t
    val of_bool_var : Ident.tvar -> t
    val of_neg_bool_var : Ident.tvar -> t
    val of_bool_term : term -> t
    val of_neg_bool_term : term -> t
    val insert_let_pvar_app : Ident.tvar -> Sort.t -> term -> info -> t -> t

    (** Destruction *)

    val let_app : t -> predicate * term list * info
    val let_psym_app : t -> pred_sym * term list * info
    val let_pvar_app : t -> Ident.pvar * Sort.t list * term list * info
    val info_of_true : t -> info
    val info_of_false : t -> info
    val info_of : t -> info
    val pvar_of : t -> Ident.pvar

    (** Morphism *)

    val map_term : f:(term -> term) -> t -> t
    val iter_term : f:(term -> unit) -> t -> unit

    (** Printing *)

    val str_of : ?priority:Priority.t -> t -> string

    (** Observation *)

    val is_true : t -> bool
    val is_false : t -> bool
    val is_app : t -> bool
    val is_psym_app : t -> bool
    val is_pvar_app : t -> bool
    val is_pvar_app_of : Ident.pvar -> t -> bool
    val is_let_free : t -> bool
    val is_quantifier_free : t -> bool
    val tvs_of : t -> Ident.tvar_set
    val pvs_of : t -> Ident.pvar_set
    val fvs_of : t -> Ident.tvar_set
    val svs_of : t -> Ident.svar_set
    val term_sort_env_of : ?bvs:Ident.tvar_set -> t -> sort_env_set
    val pred_sort_env_of : ?bpvs:Ident.pvar_set -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:Ident.pvar_set -> t -> sort_env_set
    val occur : Ident.pvar -> t -> bool
    val atoms_of : ?pos:bool -> t -> t Set.Poly.t * t Set.Poly.t
    val funsyms_of : t -> fun_sym Set.Poly.t
    val predsyms_of : t -> pred_sym Set.Poly.t
    val pathexps_of : ?bvs:Ident.tvar_set -> t -> term Set.Poly.t
    val filtered_terms_of : f:(term -> bool) -> t -> term Set.Poly.t
    val terms_of : t -> term Set.Poly.t
    val fvar_apps_of : t -> term Set.Poly.t
    val nesting_level : t -> int
    val number_of_quantifiers : t -> int

    val number_of_pvar_apps :
      ?ex:(Ident.tvar, int) Map.Poly.t -> bool -> t -> int

    val count_pvar_apps : t -> (Ident.pvar * (int * int)) list
    val ast_size : t -> int

    val occur_times :
      ?map:(Ident.tvar, int) Map.Poly.t -> Ident.tvar -> t -> int

    val let_env_of : ?map:termSubst -> t -> termSubst
    val let_sort_env_of : ?map:sort_env_map -> t -> sort_env_map
    val div_rem_of : t -> (term * term) Set.Poly.t

    (** Substitution *)

    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t

    val rename_sorted_pvars :
      (string * Sort.t list, Ident.pvar) Map.Poly.t -> t -> t

    val alpha_rename_let : ?map:Ident.tvar_map -> t -> t
    val refresh_tvar : sort_env_map * t -> sort_env_map * t
    val subst : termSubst -> t -> t
    val subst_preds : predSubst -> t -> formula
    val subst_funcs : funcSubst -> t -> t
    val subst_neg : Ident.pvar -> t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val aconv_tvar : t -> t
    val aconv_tvar_norm : (unit -> Ident.tvar) -> t -> t
    val aconv_pvar : t -> t

    (** Transformation *)

    val negate : ?negate_formula:(formula -> formula) -> t -> t option
    val complete_psort : pred_sort_env_map -> t -> t
    val elim_neq : t -> formula
    val elim_ite : t -> formula
    val elim_ite_prob : (formula -> formula) -> t -> formula Set.Poly.t
    val instantiate_div0_mod0 : t -> t

    val replace_div_mod :
      (term * term, Ident.tvar * Ident.tvar) Map.Poly.t -> t -> t

    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t
    val instantiate : t -> t

    (** Unification and Pattern Matching *)

    val unify : Ident.tvar_set -> t -> t -> termSubst option
    val pattern_match : Ident.tvar_set -> t -> t -> termSubst option
  end

  module type FormulaType = sig
    type term
    type atom
    type rand
    type predicate_fixpoint
    type termSubst
    type predSubst
    type funcSubst
    type unop = Not
    type binop = And | Or | Imply | Iff | Xor
    type binder = Forall | Exists | Random of rand

    type t =
      | Atom of atom * info
      | UnaryOp of unop * t * info
      | BinaryOp of binop * t * t * info
      | Bind of binder * sort_env_list * t * info
      | LetRec of t def list * t * info
      | LetFormula of Ident.tvar * Sort.t * term * t * info

    and 'a def = {
      kind : predicate_fixpoint;
      name : Ident.pvar;
      args : sort_env_list;
      body : 'a;
    }

    (** Sorts *)

    val subst_sorts_bounds : sort_subst -> sort_env_list -> sort_env_list
    val subst_conts_bounds : eff_subst -> sort_env_list -> sort_env_list
    val subst_opsigs_bounds : opsig_subst -> sort_env_list -> sort_env_list

    (** Binders *)

    val flip_quantifier : binder -> binder
    val str_of_binder : binder -> string
    val flip_binop : binop -> binop
    val str_of_unop : unop -> string
    val str_of_binop : binop -> string

    (** Construction *)

    val mk_atom : ?info:info -> atom -> t
    val mk_unop : ?info:info -> unop -> t -> t
    val mk_neg : ?info:info -> t -> t
    val mk_binop : ?info:info -> binop -> t -> t -> t
    val mk_and : ?info:info -> t -> t -> t
    val mk_or : ?info:info -> t -> t -> t
    val mk_imply : ?info:info -> t -> t -> t
    val mk_iff : ?info:info -> t -> t -> t
    val mk_xor : ?info:info -> t -> t -> t
    val mk_bind : ?info:info -> binder -> sort_env_list -> t -> t
    val mk_binds : (binder * sort_env_list) list -> t -> t
    val mk_bind_if_bounded : ?info:info -> binder -> sort_env_list -> t -> t
    val mk_forall : ?info:info -> sort_env_list -> t -> t
    val mk_exists : ?info:info -> sort_env_list -> t -> t
    val mk_forall_if_bounded : ?info:info -> sort_env_list -> t -> t
    val mk_exists_if_bounded : ?info:info -> sort_env_list -> t -> t
    val mk_random : ?info:info -> rand -> sort_env_list -> t -> t
    val mk_randoms : (Ident.tvar * rand) list -> t -> t
    val mk_let_formula : ?info:info -> Ident.tvar -> Sort.t -> term -> t -> t
    val mk_letrec : ?info:info -> t def list -> t -> t
    val mk_false : ?info:info -> unit -> t
    val mk_true : ?info:info -> unit -> t
    val mk_bool : bool -> t
    val negate : t -> t
    val of_bool_var : Ident.tvar -> t
    val of_neg_bool_var : Ident.tvar -> t
    val of_bool_term : term -> t
    val of_neg_bool_term : term -> t
    val and_of : t list -> t
    val or_of : t list -> t
    val xor_of : t list -> t
    val geq : term -> term -> t
    val gt : term -> term -> t
    val leq : term -> term -> t
    val lt : term -> term -> t
    val eq : term -> term -> t
    val eqs : term list -> t list
    val neq : term -> term -> t
    val mk_range : term -> Z.t -> Z.t -> t list
    val mk_range_opt : term -> Z.t option -> Z.t option -> t list
    val mk_range_real : term -> Q.t -> Q.t -> t list
    val mk_range_real_opt : term -> Q.t option -> Q.t option -> t list

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
    val let_letrec : t -> t def list * t * info
    val body_of_let : t -> t

    (** Morphism *)

    val map_funcs : f:('a -> 'b) -> 'a def list -> 'b def list

    val fold :
      f:
        < fatom : atom -> 'a
        ; fbind : binder -> sort_env_list -> 'a -> 'a
        ; fletrec : 'a def list -> 'a -> 'a
        ; fnot : 'a -> 'a
        ; fand : 'a -> 'a -> 'a
        ; for_ : 'a -> 'a -> 'a
        ; fimply : 'a -> 'a -> 'a
        ; fiff : 'a -> 'a -> 'a
        ; fxor : 'a -> 'a -> 'a
        ; flet : Ident.tvar -> Sort.t -> term -> 'a -> 'a > ->
      t ->
      'a

    val map_term : f:(term -> term) -> t -> t
    val iter_term : f:(term -> unit) -> t -> unit
    val map_atom : f:(atom -> t) -> t -> t
    val map_atom_polarity : f:(bool -> atom -> t) -> t -> bool -> t
    val iter_atom : f:(atom -> unit) -> t -> unit

    (** Printing *)

    val str_of : ?priority:Priority.t -> t -> string

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
    val is_let_free : t -> bool
    val is_quantifier_free : t -> bool
    val tvs_of : t -> Ident.tvar_set
    val pvs_of : t -> Ident.pvar_set
    val fvs_of : t -> Ident.tvar_set
    val svs_of : t -> Ident.svar_set
    val term_sort_env_of : ?bvs:Ident.tvar_set -> t -> sort_env_set
    val pred_sort_env_of : ?bpvs:Ident.pvar_set -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:Ident.pvar_set -> t -> sort_env_set
    val conjuncts_of : t -> t Set.Poly.t
    val conjuncts_list_of : t -> t list
    val disjuncts_of : t -> t Set.Poly.t
    val disjuncts_list_of : t -> t list
    val funsyms_of : t -> fun_sym Set.Poly.t
    val predsyms_of : t -> pred_sym Set.Poly.t
    val pathexps_of : ?bvs:Ident.tvar_set -> t -> term Set.Poly.t
    val terms_of : t -> term Set.Poly.t
    val fvar_apps_of : t -> term Set.Poly.t
    val filtered_terms_of : f:(term -> bool) -> t -> term Set.Poly.t

    val atoms_of :
      ?nrec:bool -> ?pos:bool -> t -> atom Set.Poly.t * atom Set.Poly.t

    val let_env_of : ?map:termSubst -> t -> termSubst
    val let_sort_env_of : ?map:sort_env_map -> t -> sort_env_map
    val div_rem_of : t -> (term * term) Set.Poly.t
    val nesting_level : t -> int
    val number_of_quantifiers : t -> int

    val number_of_pvar_apps :
      ?ex:(Ident.tvar, int) Map.Poly.t -> bool -> t -> int

    val count_pvar_apps : t -> (Ident.pvar * (int * int)) list
    val ast_size : t -> int

    val occur_times :
      ?map:(Ident.tvar, int) Map.Poly.t -> Ident.tvar -> t -> int

    (** Construction *)

    val bind : ?info:info -> binder -> sort_env_list -> t -> t
    val forall : ?info:info -> sort_env_list -> t -> t
    val exists : ?info:info -> sort_env_list -> t -> t
    val bind_fvs : binder -> t -> t
    val bind_fvs_with_forall : t -> t
    val bind_fvs_with_exists : t -> t
    val quantify_except : ?exists:bool -> Ident.tvar_set -> t -> int * t

    (** Substitution *)

    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t

    val rename_sorted_pvars :
      (string * Sort.t list, Ident.pvar) Map.Poly.t -> t -> t

    val alpha_rename_let : ?map:Ident.tvar_map -> t -> t
    val refresh_tvar : sort_env_map * t -> sort_env_map * t
    val refresh_except : Ident.tvar_set -> t -> sort_env_map * t
    val replace_let_body : t -> t -> t
    val replace_let_term_body : term -> t -> t
    val subst : termSubst -> t -> t
    val subst_preds : predSubst -> t -> t
    val subst_funcs : funcSubst -> t -> t
    val subst_neg : Ident.pvar -> t -> t
    val aconv_tvar : t -> t
    val aconv_tvar_norm : (unit -> Ident.tvar) -> t -> t
    val aconv_pvar : t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val subst_sorts_pred : sort_subst -> Ident.tvar * t -> Ident.tvar * t
    val apply_pred : Ident.tvar * t -> term -> t

    (** Construction *)

    val insert_let_formula : Ident.tvar -> Sort.t -> term -> info -> t -> t

    (** Transformation *)

    val reduce_sort_map : sort_env_map * t -> sort_env_map * t
    val complete_psort : pred_sort_env_map -> t -> t
    val complete_tsort : termSubst -> t -> t
    val rm_quant : ?forall:bool -> t -> sort_env_set * t
    val move_quantifiers_to_front : t -> t
    val elim_neq : t -> t
    val elim_ite : t -> t
    val elim_pvars : Ident.tvar_set -> t -> t
    val elim_let_with_unknowns : ?map:termSubst -> Ident.tvar_set -> t -> t
    val elim_let : ?map:termSubst -> t -> t
    val elim_unused_bounds : t -> t
    val elim_let_equisat : t -> sort_env_map * t
    val elim_let_equivalid : t -> sort_env_map * t
    val elim_let_equi : bool -> t -> t
    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t
    val instantiate_div0_mod0 : t -> t

    val replace_div_mod :
      (term * term, Ident.tvar * Ident.tvar) Map.Poly.t -> t -> t

    val rm_div_mod : t -> t
    val rm_atom : ?polarity:bool -> ?is_and:bool -> f:(atom -> bool) -> t -> t
    val to_atom : t -> atom
    val univ_clos : t -> t
    val split_exists : t -> sort_env_list * t
    val split_quantifiers : t -> (binder * sort_env_list) list * t
    val nnf_of : t -> t

    val dnf_of :
      ?process_pure:bool ->
      sort_env_map ->
      t ->
      (atom Set.Poly.t * atom Set.Poly.t * t) Set.Poly.t

    val cnf_of :
      ?process_pure:bool ->
      sort_env_map ->
      t ->
      (atom Set.Poly.t * atom Set.Poly.t * t) Set.Poly.t

    val pnf_of : t -> t

    val skolemize :
      use_fn_pred:bool ->
      only_impure:bool ->
      t ->
      sort_env_map * sort_env_map * t

    (** Observation *)

    val psym_pvar_apps_of :
      ?simplifier:(t -> t) -> t -> atom list * atom list * atom list
  end

  module type T_boolType = sig
    type formula
    type atom
    type term
    type fun_sym += Formula of formula | IfThenElse
    type pred_sym += Eq | Neq
    type Sort.t += SBool

    (** Construction *)

    val of_atom : ?info:info -> atom -> term
    val of_formula : ?info:info -> formula -> term
    val mk_true : ?info:info -> unit -> term
    val mk_false : ?info:info -> unit -> term
    val make : ?info:info -> bool -> term
    val mk_eq : ?info:info -> term -> term -> atom
    val mk_neq : ?info:info -> term -> term -> atom
    val mk_eqs : term list -> atom list
    val mk_if_then_else : ?info:info -> term -> term -> term -> term
    val ifte : ?info:info -> formula -> term -> term -> term
    val negate : term -> term

    (** Destruction *)

    val let_bool : term -> bool
    val let_formula : term -> formula

    (** Observation *)

    val is_atom : term -> bool
    val is_true : term -> bool
    val is_false : term -> bool
    val is_formula : term -> bool
    val is_sbool : term -> bool
  end

  module type T_intType = sig
    type iterm
    type iatom

    type fun_sym +=
      | Int of Z.t
      | Neg
      | Nop
      | Abs
      | Add
      | Sub
      | Mul
      | Div of Value.modulo
      | Rem of Value.modulo
      | Power

    type pred_sym += Leq | Geq | Lt | Gt | PDiv | NotPDiv
    type Sort.t += SInt | SRefInt | SUnrefInt

    (** Construction *)

    val mk_int : ?info:info -> Z.t -> iterm
    val from_int : ?info:info -> int -> iterm
    val zero : ?info:info -> unit -> iterm
    val one : ?info:info -> unit -> iterm
    val hundred : ?info:info -> unit -> iterm
    val mk_neg : ?info:info -> iterm -> iterm
    val mk_abs : ?info:info -> iterm -> iterm
    val mk_add : ?info:info -> iterm -> iterm -> iterm
    val mk_sub : ?info:info -> iterm -> iterm -> iterm
    val mk_mul : ?info:info -> iterm -> iterm -> iterm
    val mk_div : ?info:info -> Value.modulo -> iterm -> iterm -> iterm
    val mk_rem : ?info:info -> Value.modulo -> iterm -> iterm -> iterm
    val mk_power : ?info:info -> iterm -> iterm -> iterm
    val mk_min : ?info:info -> iterm -> iterm -> iterm
    val mk_max : ?info:info -> iterm -> iterm -> iterm
    val mk_sum : ?info:info -> iterm -> iterm list -> iterm
    val mk_prod : ?info:info -> iterm -> iterm list -> iterm
    val mk_leq : ?info:info -> iterm -> iterm -> iatom
    val mk_geq : ?info:info -> iterm -> iterm -> iatom
    val mk_lt : ?info:info -> iterm -> iterm -> iatom
    val mk_gt : ?info:info -> iterm -> iterm -> iatom
    val mk_pdiv : ?info:info -> iterm -> iterm -> iatom
    val mk_not_pdiv : ?info:info -> iterm -> iterm -> iatom
    val l1_norm : iterm list -> iterm
    val l2_norm_sq : iterm list -> iterm

    (** Destruction *)

    val let_int : iterm -> Z.t
    val let_neg : iterm -> iterm * info
    val let_abs : iterm -> iterm * info
    val let_add : iterm -> iterm * iterm * info
    val let_sub : iterm -> iterm * iterm * info
    val let_mul : iterm -> iterm * iterm * info
    val let_div : iterm -> Value.modulo * iterm * iterm * info
    val let_rem : iterm -> Value.modulo * iterm * iterm * info
    val let_power : iterm -> iterm * iterm * info
    val let_leq : iatom -> iterm * iterm * info
    val let_geq : iatom -> iterm * iterm * info
    val let_lt : iatom -> iterm * iterm * info
    val let_gt : iatom -> iterm * iterm * info
    val let_pdiv : iatom -> iterm * iterm * info
    val let_not_pdiv : iatom -> iterm * iterm * info

    (** Observation *)

    val is_sint : iterm -> bool
    val is_int : iterm -> bool
    val is_zero : iterm -> bool
    val is_unit : iterm -> bool
    val is_minus_one : iterm -> bool
    val is_neg : iterm -> bool
    val is_abs : iterm -> bool
    val is_add : iterm -> bool
    val is_sub : iterm -> bool
    val is_mul : iterm -> bool
    val is_div : iterm -> bool
    val is_rem : iterm -> bool
    val is_power : iterm -> bool
    val is_leq : iatom -> bool
    val is_geq : iatom -> bool
    val is_lt : iatom -> bool
    val is_gt : iatom -> bool
    val is_pdiv : iatom -> bool
    val is_not_pdiv : iatom -> bool
  end

  module type T_realType = sig
    type rterm
    type ratom

    type fun_sym +=
      | Real of Q.t
      | Alge of int
      | RNeg
      | RAbs
      | RAdd
      | RSub
      | RMul
      | RDiv
      | RPower

    type pred_sym += RLeq | RGeq | RLt | RGt
    type Sort.t += SReal

    (** Construction *)

    val mk_real : ?info:info -> Q.t -> rterm
    val mk_alge : ?info:info -> rterm -> int -> rterm
    val rzero : ?info:info -> unit -> rterm
    val rone : ?info:info -> unit -> rterm
    val mk_rneg : ?info:info -> rterm -> rterm
    val mk_rabs : ?info:info -> rterm -> rterm
    val mk_radd : ?info:info -> rterm -> rterm -> rterm
    val mk_rsub : ?info:info -> rterm -> rterm -> rterm
    val mk_rmul : ?info:info -> rterm -> rterm -> rterm
    val mk_rdiv : ?info:info -> rterm -> rterm -> rterm
    val mk_rpower : ?info:info -> rterm -> rterm -> rterm
    val mk_rmin : ?info:info -> rterm -> rterm -> rterm
    val mk_rmax : ?info:info -> rterm -> rterm -> rterm
    val mk_rsum : ?info:info -> rterm -> rterm list -> rterm
    val mk_rprod : ?info:info -> rterm -> rterm list -> rterm
    val mk_rleq : ?info:info -> rterm -> rterm -> ratom
    val mk_rgeq : ?info:info -> rterm -> rterm -> ratom
    val mk_rlt : ?info:info -> rterm -> rterm -> ratom
    val mk_rgt : ?info:info -> rterm -> rterm -> ratom
    val l1_norm : rterm list -> rterm
    val l2_norm_sq : rterm list -> rterm

    (** Destruction *)

    val let_real : rterm -> Q.t
    val let_alge : rterm -> rterm * int
    val let_rneg : rterm -> rterm * info
    val let_rabs : rterm -> rterm * info
    val let_radd : rterm -> rterm * rterm * info
    val let_rsub : rterm -> rterm * rterm * info
    val let_rmul : rterm -> rterm * rterm * info
    val let_rdiv : rterm -> rterm * rterm * info
    val let_rpower : rterm -> rterm * rterm * info
    val let_rleq : ratom -> rterm * rterm * info
    val let_rgeq : ratom -> rterm * rterm * info
    val let_rlt : ratom -> rterm * rterm * info
    val let_rgt : ratom -> rterm * rterm * info

    (** Observation *)

    val is_sreal : rterm -> bool
    val is_real : rterm -> bool
    val is_alge : rterm -> bool
    val is_rzero : rterm -> bool
    val is_runit : rterm -> bool
    val is_rminus_one : rterm -> bool
    val is_rneg : rterm -> bool
    val is_rabs : rterm -> bool
    val is_radd : rterm -> bool
    val is_rsub : rterm -> bool
    val is_rmul : rterm -> bool
    val is_rdiv : rterm -> bool
    val is_rpower : rterm -> bool
    val is_rleq : ratom -> bool
    val is_rgeq : ratom -> bool
    val is_rlt : ratom -> bool
    val is_rgt : ratom -> bool
  end

  module type T_bvType = sig
    type bvterm
    type bvatom
    type size = int (* bits *) option
    type signed = bool (* signed/unsigned *) option

    type fun_sym +=
      | BVNum of size * Z.t
      | BVNot of size
      | BVAnd of size
      | BVOr of size
      | BVXor of size
      | BVNand of size
      | BVNor of size
      | BVXnor of size
      | BVNeg of size
      | BVAdd of size
      | BVSub of size
      | BVMul of size
      | BVDiv of size * signed
      | BVRem of size * signed
      | BVSMod of size
      | BVSHL of size
      | BVLSHR of size
      | BVASHR of size
      | BVEXTRACT of size * int * int
      | BVSEXT of size * int
      | BVZEXT of size * int
      | BVCONCAT of size * size

    type pred_sym +=
      | BVLeq of size * signed
      | BVGeq of size * signed
      | BVLt of size * signed
      | BVGt of size * signed

    type Sort.t += SBV of size

    (** Construction *)

    val mk_bvnum : ?info:info -> size:size -> Z.t -> bvterm
    val mk_bvnot : ?info:info -> size:size -> bvterm -> bvterm
    val mk_bvand : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvor : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvxor : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvnand : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvnor : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvxnor : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvneg : ?info:info -> size:size -> bvterm -> bvterm
    val mk_bvadd : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvsub : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvmul : ?info:info -> size:size -> bvterm -> bvterm -> bvterm

    val mk_bvdiv :
      ?info:info -> size:size -> signed:signed -> bvterm -> bvterm -> bvterm

    val mk_bvrem :
      ?info:info -> size:size -> signed:signed -> bvterm -> bvterm -> bvterm

    val mk_bvsmod : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvshl : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvlshr : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvashr : ?info:info -> size:size -> bvterm -> bvterm -> bvterm
    val mk_bvextract : ?info:info -> size:size -> int -> int -> bvterm -> bvterm
    val mk_bvsext : ?info:info -> size:size -> int -> bvterm -> bvterm
    val mk_bvzext : ?info:info -> size:size -> int -> bvterm -> bvterm

    val mk_bvconcat :
      ?info:info -> size1:size -> size2:size -> bvterm -> bvterm -> bvterm

    val mk_bvleq :
      ?info:info -> size:size -> signed:signed -> bvterm -> bvterm -> bvatom

    val mk_bvgeq :
      ?info:info -> size:size -> signed:signed -> bvterm -> bvterm -> bvatom

    val mk_bvlt :
      ?info:info -> size:size -> signed:signed -> bvterm -> bvterm -> bvatom

    val mk_bvgt :
      ?info:info -> size:size -> signed:signed -> bvterm -> bvterm -> bvatom

    val bvzero : ?info:info -> size:size -> unit -> bvterm
    val bvone : ?info:info -> size:size -> unit -> bvterm
    val mk_bvsum : ?info:info -> size:size -> bvterm -> bvterm list -> bvterm

    (** Destruction *)

    val let_bv : bvterm -> size * Z.t
    val let_bvnot : bvterm -> size * bvterm * info
    val let_bvand : bvterm -> size * bvterm * bvterm * info
    val let_bvor : bvterm -> size * bvterm * bvterm * info
    val let_bvxor : bvterm -> size * bvterm * bvterm * info
    val let_bvnand : bvterm -> size * bvterm * bvterm * info
    val let_bvnor : bvterm -> size * bvterm * bvterm * info
    val let_bvxnor : bvterm -> size * bvterm * bvterm * info
    val let_bvneg : bvterm -> size * bvterm * info
    val let_bvadd : bvterm -> size * bvterm * bvterm * info
    val let_bvsub : bvterm -> size * bvterm * bvterm * info
    val let_bvmul : bvterm -> size * bvterm * bvterm * info
    val let_bvdiv : bvterm -> size * signed * bvterm * bvterm * info
    val let_bvrem : bvterm -> size * signed * bvterm * bvterm * info
    val let_bvsmod : bvterm -> size * bvterm * bvterm * info
    val let_bvshl : bvterm -> size * bvterm * bvterm * info
    val let_bvlshr : bvterm -> size * bvterm * bvterm * info
    val let_bvashr : bvterm -> size * bvterm * bvterm * info
    val let_bvextract : bvterm -> size * int * int * bvterm * info
    val let_bvsext : bvterm -> size * int * bvterm * info
    val let_bvzext : bvterm -> size * int * bvterm * info
    val let_bvconcat : bvterm -> size * size * bvterm * bvterm * info
    val let_bvleq : bvatom -> size * signed * bvterm * bvterm * info
    val let_bvgeq : bvatom -> size * signed * bvterm * bvterm * info
    val let_bvlt : bvatom -> size * signed * bvterm * bvterm * info
    val let_bvgt : bvatom -> size * signed * bvterm * bvterm * info

    (** Observation *)

    val bits_of : size -> int
    val signed_of : signed -> bool
    val is_bv_fsym : fun_sym -> bool
    val is_bv_psym : pred_sym -> bool
    val is_sbv : bvterm -> bool
    val is_bv : bvterm -> bool
    val is_bvzero : bvterm -> bool
    val is_bvunit : bvterm -> bool
    val is_bvnot : bvterm -> bool
    val is_bvand : bvterm -> bool
    val is_bvor : bvterm -> bool
    val is_bvxor : bvterm -> bool
    val is_bvnand : bvterm -> bool
    val is_bvnor : bvterm -> bool
    val is_bvxnor : bvterm -> bool
    val is_bvneg : bvterm -> bool
    val is_bvadd : bvterm -> bool
    val is_bvsub : bvterm -> bool
    val is_bvmul : bvterm -> bool
    val is_bvdiv : bvterm -> bool
    val is_bvrem : bvterm -> bool
    val is_bvsmod : bvterm -> bool
    val is_bvshl : bvterm -> bool
    val is_bvlshr : bvterm -> bool
    val is_bvashr : bvterm -> bool
    val is_bvextract : bvterm -> bool
    val is_bvsext : bvterm -> bool
    val is_bvzext : bvterm -> bool
    val is_bvconcat : bvterm -> bool
    val is_bvleq : bvatom -> bool
    val is_bvgeq : bvatom -> bool
    val is_bvlt : bvatom -> bool
    val is_bvgt : bvatom -> bool
    val str_of_size : size -> string
    val str_of_signed : signed -> string

    (** Size manipulation *)

    val eq_size : size -> size -> bool
    val merge_size : size -> size -> size
    val geq_size : size -> size -> bool
    val ext_size : size -> int -> size
    val add_size : size -> size -> size
    val max_size : size -> size -> size
    val max_size_list : size list -> size
  end

  module type T_irbType = sig
    include T_intType
    include T_realType
    include T_bvType

    type term
    type atom
    type formula

    type fun_sym +=
      | IntToReal
      | RealToInt
      | IntToBV of size
      | BVToInt of size * signed

    type pred_sym += IsInt

    (** Construction *)

    val mk_int_to_real : ?info:info -> term -> term
    val mk_real_to_int : ?info:info -> term -> term
    val mk_int_to_bv : ?info:info -> size:size -> term -> term
    val mk_bv_to_int : ?info:info -> size:size -> signed:signed -> term -> term
    val mk_is_int : ?info:info -> term -> atom
    val to_int_if_rb : term -> term
    val to_real_if_int : term -> term

    (** Destruction *)

    val is_sint_sreal : term -> bool
    val is_sirb : term -> bool
    val is_int_to_real : term -> bool
    val is_real_to_int : term -> bool
    val is_int_to_bv : term -> bool
    val is_bv_to_int : term -> bool
    val is_is_int : atom -> bool

    (** Observation *)

    val let_int_to_real : term -> term * info
    val let_real_to_int : term -> term * info
    val let_int_to_bv : term -> size * term * info
    val let_bv_to_int : term -> size * signed * term * info
    val let_is_int : atom -> term * info
    val origin_of : Sort.t list -> term list

    (* Auxliary functions for templates *)
    val bool_terms_of : (term * Sort.t) list -> (term * Sort.t) list
    val num_terms_of : (term * Sort.t) list -> (term * Sort.t) list
    val num_sort_of : (term * Sort.t) list -> Sort.t

    val eq_of :
      Sort.t -> (term * Sort.t) list -> (term list * term) list * formula

    val ineq_of :
      Sort.t -> (term * Sort.t) list -> (term list * term) list * formula

    val br_bools_of :
      ((term * Sort.t) list -> (term list * term) list * formula) ->
      (term * Sort.t) list ->
      (term list * term) list * formula
  end

  module type T_numType = sig
    type term
    type atom

    type fun_sym +=
      | Value of string * Ident.svar
      | NNeg of Ident.svar
      | NSEXT of int option * Ident.svar * int * Ident.svar
      | NAdd of Ident.svar
      | NSub of Ident.svar
      | NMul of Ident.svar
      | NDiv of Ident.svar * Value.modulo
      | NRem of Ident.svar * Value.modulo
      | NPower of Ident.svar

    type pred_sym +=
      | NLeq of Ident.svar
      | NGeq of Ident.svar
      | NLt of Ident.svar
      | NGt of Ident.svar

    exception NotValue

    (** Construction *)

    val mk_value : ?info:info -> string -> term
    val mk_neg_value : ?info:info -> string -> term
    val mk_nneg : ?info:info -> term -> term
    val mk_nsext : ?info:info -> size:int option -> int -> term -> term
    val mk_nadd : ?info:info -> term -> term -> term
    val mk_nsub : ?info:info -> term -> term -> term
    val mk_nmul : ?info:info -> term -> term -> term
    val mk_ndiv : ?info:info -> Value.modulo -> term -> term -> term
    val mk_nrem : ?info:info -> Value.modulo -> term -> term -> term
    val mk_npower : ?info:info -> term -> term -> term
    val mk_ngeq : ?info:info -> term -> term -> atom
    val mk_nleq : ?info:info -> term -> term -> atom
    val mk_ngt : ?info:info -> term -> term -> atom
    val mk_nlt : ?info:info -> term -> term -> atom

    (** Destruction *)

    val let_value : term -> string * info
    val let_nneg : term -> term * info
    val let_nsext : term -> int option * int * term * info
    val let_nadd : term -> term * term * info
    val let_nsub : term -> term * term * info
    val let_nmul : term -> term * term * info
    val let_ndiv : term -> term * term * info
    val let_nrem : term -> term * term * info
    val let_npower : term -> term * term * info
    val let_ngeq : atom -> term * term * info
    val let_nleq : atom -> term * term * info
    val let_ngt : atom -> term * term * info
    val let_nlt : atom -> term * term * info

    (** Observation *)

    val is_nneg : term -> bool
    val is_nsext : term -> bool
    val is_nadd : term -> bool
    val is_nsub : term -> bool
    val is_nmul : term -> bool
    val is_ndiv : term -> bool
    val is_nrem : term -> bool
    val is_npower : term -> bool
    val is_ngeq : atom -> bool
    val is_nleq : atom -> bool
    val is_ngt : atom -> bool
    val is_nlt : atom -> bool
    val is_value : term -> bool

    (** Function Symbols *)

    val fsym_of_num_fsym : fun_sym -> Sort.t list -> fun_sym
    val psym_of_num_psym : pred_sym -> Sort.t -> pred_sym
  end

  module type T_refType = sig
    type term
    type Sort.t += SRef of Sort.t
    type fun_sym += Ref of Sort.t | Deref of Sort.t | Update of Sort.t

    (** Construction *)

    val mk_ref : Sort.t -> term -> term
    val mk_deref : Sort.t -> term -> term
    val mk_update : Sort.t -> term -> term -> term

    (** Observation *)

    val is_ref_sort : Sort.t -> bool
    val eval_select : term -> term option
  end

  module type T_arrayType = sig
    type term
    type atom

    type fun_sym +=
      | AConst of Sort.t * Sort.t
      | AStore of Sort.t * Sort.t
      | ASelect of Sort.t * Sort.t

    type Sort.t += SArray of Sort.t * Sort.t

    (** Sorts *)

    val is_sarray : Sort.t -> bool
    val mk_array_sort : Sort.t -> Sort.t -> Sort.t
    val of_arrow : Sort.t -> Sort.t
    val index_sort_of : Sort.t -> Sort.t
    val elem_sort_of : Sort.t -> Sort.t

    (** Construction *)

    val mk_const_array : Sort.t -> Sort.t -> term -> term
    val mk_store : Sort.t -> Sort.t -> term -> term -> term -> term
    val mk_select : Sort.t -> Sort.t -> term -> term -> term
    val of_fvar_app : term -> term

    (** Destruction *)

    val let_store : term -> Sort.t * Sort.t * term * term * term * info
    val let_select : term -> Sort.t * Sort.t * term * term * info

    (** Observation *)

    val is_store : term -> bool
    val is_select : term -> bool
    val eval_select : term -> term -> term option
    val non_stored : term -> term -> bool
  end

  module type T_tupleType = sig
    type term
    type atom
    type Sort.t += STuple of Sort.t list
    type fun_sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int
    type pred_sym += IsTuple of Sort.t list | NotIsTuple of Sort.t list

    (** Sorts *)

    val let_stuple : Sort.t -> Sort.t list

    (** Construction *)

    val mk_tuple_cons : Sort.t list -> term list -> term
    val mk_tuple_sel : Sort.t list -> term -> int -> term
    val mk_is_tuple : Sort.t list -> term -> atom
    val mk_is_not_tuple : Sort.t list -> term -> atom

    (** Destruction *)

    val let_tuple_cons : term -> Sort.t list * term list * info
    val let_tuple_sel : term -> Sort.t list * int * term * info

    (** Observation *)

    val is_tuple_cons : term -> bool
    val is_tuple_sel : term -> bool
    val eval_select : term -> int -> term option
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

    type pred_sym += IsCons of string * dt | NotIsCons of string * dt
    type Sort.t += SDT of dt | SUS of string * Sort.t list

    val params_of : Sort.t -> Sort.t list
    val is_sdt : Sort.t -> bool
    val is_sus : Sort.t -> bool
    val is_dt : Sort.t -> bool
    val is_codt : Sort.t -> bool
    val is_undef : Sort.t -> bool
    val is_finite_dt : ?his:Sort.t list -> Sort.t -> bool

    (** Construction *)

    val mk_cons : ?info:info -> dt -> string -> term list -> term
    val mk_sel : ?info:info -> dt -> string -> term -> term
    val mk_sel_by_cons : ?info:info -> dt -> string -> int -> term -> term
    val mk_is_cons : ?info:info -> dt -> string -> term -> atom
    val mk_is_not_cons : ?info:info -> dt -> string -> term -> atom
    val mk_dummy : Sort.t -> term

    (** Observation *)

    val is_cons : term -> bool
    val is_sel : term -> bool
    val is_is_cons : atom -> bool
    val is_is_not_cons : atom -> bool
    val sels_of_cons : fun_sym -> dtsel list
    val base_terms_of : dt -> term list
    val size_of_cons : term -> int
    val inst_unknown_sel_term : (term -> term) -> formula -> formula
    val eval_select : string -> dt -> term -> term option
  end

  module type DatatypeType = sig
    type term
    type formula
    type sel = Sel of string * Sort.t | InSel of string * string * Sort.t list
    type cons = { name : string; sels : sel list }
    type func = FCons of cons | FSel of sel
    type flag = FDt | FCodt | Undef | Alias of Sort.t
    type dt = { name : string; params : Sort.t list; conses : cons list }
    type t = { name : string; dts : dt list; flag : flag }

    (** Construction *)

    val mk_cons : ?sels:sel list -> string -> cons
    val mk_sel : string -> Sort.t -> sel
    val mk_insel : string -> string -> Sort.t list -> sel
    val mk_dt : string -> Sort.t list -> dt
    val make : string -> dt list -> flag -> t
    val mk_uninterpreted_datatype : ?numeral:int -> string -> t
    val mk_alias : string -> Sort.t -> t
    val enum_cons_terms : int -> Sort.t -> term Set.Poly.t -> term Set.Poly.t

    (** Observation *)

    val name_of_sel : sel -> string
    val sels_of_cons : cons -> sel list
    val name_of_cons : cons -> string
    val look_up_sel_of_cons : cons -> string -> sel option
    val name_of_dt : dt -> string
    val params_of_dt : dt -> Sort.t list
    val conses_of_dt : dt -> cons list
    val full_name_of_dt : dt -> string
    val name_of : t -> string
    val flag_of : t -> flag
    val dts_of : t -> dt list
    val look_up_dt : t -> string -> dt option
    val dt_of : t -> dt
    val conses_of : t -> cons list
    val base_conses_of : t -> cons list
    val sels_of : t -> sel list
    val params_of : t -> Sort.t list
    val look_up_cons : t -> string -> cons option
    val look_up_sel : t -> string -> sel option
    val look_up_cons_of_sel : t -> string -> cons option
    val look_up_func : t -> string -> func option
    val look_up_base_cons : t -> cons option
    val full_name_of : t -> string
    val short_name_of : t -> string
    val sort_of : t -> Sort.t
    val svs_of : t -> Ident.svar_set
    val evs_of : t -> Ident.evar_set
    val rvs_of : t -> Ident.rvar_set
    val pat_match_sort : t -> t -> opsig_subst * sort_subst * eff_subst
    val is_dt : t -> bool
    val is_codt : t -> bool
    val is_undef : t -> bool
    val is_alias : t -> bool
    val is_poly : t -> bool
    val is_base : t -> string -> bool
    val is_sel : sel -> bool
    val is_insel : sel -> bool
    val is_fcons : func -> bool
    val is_fsel : func -> bool

    (** Printing *)

    val str_of_sel : sel -> string
    val str_of_cons : cons -> string
    val str_of_flag : flag -> string
    val str_of : t -> string
    val full_str_of_sel : t -> sel -> string
    val full_str_of_cons : t -> cons -> string

    (** Transformation *)

    val update_name : t -> string -> t
    val update_dts : t -> dt list -> t
    val update_dt : t -> dt -> t
    val add_cons : t -> cons -> t
    val add_sel : cons -> sel -> cons
    val update_conses : t -> cons list -> t
    val update_params : t -> Sort.t list -> t

    (** Substitution *)

    val subst_sorts_dt : sort_subst -> dt -> dt
    val subst_conts_dt : eff_subst -> dt -> dt
    val subst_opsigs_dt : opsig_subst -> dt -> dt
    val subst_dt : opsig_subst * sort_subst * eff_subst -> dt -> dt
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val subst : opsig_subst * sort_subst * eff_subst -> t -> t
    val fresh_conts_sort_dt : dt -> dt
    val fresh_rvs_sort_dt : dt -> dt
    val fresh_conts_sort : t -> t
    val fresh_rvs_sort : t -> t
    val fresh_of : t -> t

    (** Observation *)

    val sort_of_sel : t -> sel -> Sort.t
    val sorts_of_cons : t -> cons -> Sort.t list
    val sorts_of_cons_name : t -> string -> Sort.t list
    val full_dts_of : t -> dt list
    val is_finite : t -> bool
    val is_singleton : Sort.t -> bool
    val fsym_of_cons : t -> cons -> fun_sym
    val fsym_of_sel : t -> sel -> fun_sym
    val fsym_of_func : t -> func -> fun_sym
    val used_dt_and_sorts_of : t -> t Set.Poly.t * Sort.t Set.Poly.t

    val size_fun_of :
      t -> Ident.tvar * (sort_env_list * Sort.t * term * bool * formula)

    val app_size_fun : t -> term -> term

    (** Datatypes *)

    val mk_name_of_sel : string -> int -> string
    val mk_unit_dt : unit -> t
    val mk_option_dt : unit -> t
    val mk_list_dt : unit -> t
    val mk_exn_dt : unit -> t
    val mk_unit : unit -> term
    val mk_unit_sort : unit -> Sort.t
    val is_unit_sort : Sort.t -> bool
    val is_option_sort : Sort.t -> bool
    val is_list_sort : Sort.t -> bool
    val is_exn_sort : Sort.t -> bool
  end

  module type T_stringType = sig
    type term
    type Sort.t += SString
    type fun_sym += StrConst of string

    val make : string -> term
    val let_string_const : term -> string * info
  end

  module type T_sequenceType = sig
    type term
    type atom
    type Sort.t += SSequence of bool

    type fun_sym +=
      | SeqEpsilon
      | SeqSymbol of string
      | SeqConcat of bool
      | SeqLeftQuotient of bool
      | SeqRightQuotient of bool

    type pred_sym +=
      | IsPrefix of bool
      | NotIsPrefix of bool
      | SeqInRegExp of bool * string Grammar.RegWordExp.t
      | NotSeqInRegExp of bool * string Grammar.RegWordExp.t

    val mk_eps : unit -> term
    val mk_symbol : string -> term
    val mk_concat : fin:bool -> term -> term -> term
    val mk_is_prefix : bool -> term -> term -> atom
    val mk_is_not_prefix : bool -> term -> term -> atom
    val mk_is_in_regexp : bool -> string Grammar.RegWordExp.t -> term -> atom

    val mk_is_not_in_regexp :
      bool -> string Grammar.RegWordExp.t -> term -> atom
  end

  module type T_regexType = sig
    type term
    type atom
    type Sort.t += SRegEx

    type fun_sym +=
      | RegEmpty
      | RegFull
      | RegEpsilon
      | RegStr
      | RegComplement
      | RegStar
      | RegPlus
      | RegOpt
      | RegConcat
      | RegUnion
      | RegInter

    type pred_sym += StrInRegExp | NotStrInRegExp

    val mk_empty : ?info:info -> unit -> term
    val mk_full : ?info:info -> unit -> term
    val mk_eps : ?info:info -> unit -> term
    val mk_str_to_re : ?info:info -> term -> term
    val mk_complement : ?info:info -> term -> term
    val mk_star : ?info:info -> term -> term
    val mk_plus : ?info:info -> term -> term
    val mk_opt : ?info:info -> term -> term
    val mk_concat : ?info:info -> term -> term -> term
    val mk_union : ?info:info -> term -> term -> term
    val mk_inter : ?info:info -> term -> term -> term
    val mk_str_in_regexp : ?info:info -> term -> term -> atom
    val mk_not_str_in_regexp : ?info:info -> term -> term -> atom
  end

  module type TermSubstType = sig
    type term
    type t = (Ident.tvar, term) Map.Poly.t

    val str_of : t -> string
    val make : name:string -> (Ident.tvar * Sort.t) list -> term list -> t
  end

  module type PredSubstType = sig
    type formula
    type t = (Ident.pvar, sort_env_list * formula) Map.Poly.t
  end

  module type FuncSubstType = sig
    type term
    type t = (Ident.tvar, sort_env_list * term) Map.Poly.t
  end

  module type FunEnvType = sig
    type term
    type formula

    type t =
      (Ident.tvar, sort_env_list * Sort.t * term * bool * formula) Map.Poly.t

    val mk_empty : unit -> t
    val defined_formula_of : t -> formula -> formula
    val str_of : t -> string
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
    val name_is_cons : t -> string -> bool
    val name_is_sel : t -> string -> bool
    val name_is_func : t -> string -> bool
    val str_of : t -> string
    val update_dt : t -> datatype -> t
    val update_dts : t -> datatype -> t
    val force_merge : t -> t -> t
    val of_formula : formula -> t
  end

  module type RandType = sig
    type term
    type formula
    type termSubst

    type t =
      | Uniform of term * term
      | Gauss of term * term
      | IntUniform of term * term

    val mk_uniform : term -> term -> t
    val mk_gauss : term -> term -> t
    val mk_int_uniform : term -> term -> t
    val let_uniform : t -> term * term
    val let_gauss : t -> term * term
    val let_int_uniform : t -> term * term
    val subst : termSubst -> t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val sort_of : t -> Sort.t
    val str_of : t -> string
    val rename : Ident.tvar_map -> t -> t
    val mk_uniform_bounds : Ident.tvar list -> t -> formula
  end
end

let dummy_term_senv = Atomic.make []
let get_dummy_term_senv () = Atomic.get dummy_term_senv
let set_dummy_term_senv = Atomic.set dummy_term_senv
let init_dummy_term_senv () = set_dummy_term_senv []

let is_dummy_term tvar sort =
  List.exists (get_dummy_term_senv ()) ~f:(fun (tvar1, sort1) ->
      Stdlib.(tvar = tvar1)
      && match sort with Some sort -> Stdlib.(sort = sort1) | _ -> true)

let add_dummy_term tvar sort =
  if
    not (is_dummy_term tvar (Some sort (*ToDo*)))
    (*&& (Sort.is_svar sort || Sort.is_arrow sort || T_dt.is_sus sort)*)
  then set_dummy_term_senv @@ get_dummy_term_senv () @ [ (tvar, sort) ]

module rec Term :
  (Type.TermType
    with type atom := Atom.t
     and type formula := Formula.t
     and type termSubst := TermSubst.t
     and type predSubst := PredSubst.t
     and type funcSubst := FuncSubst.t
     and type dtenv := DTEnv.t) = struct
  type t =
    | Var of Ident.tvar * Sort.t * info
    | FunApp of fun_sym * t list * info
    | LetTerm of Ident.tvar * Sort.t * t * t * info

  (** Sorts *)

  let pred_to_sort_bind (pvar, sorts) =
    (Ident.pvar_to_tvar pvar (*ToDo*), Sort.mk_fun (sorts @ [ T_bool.SBool ]))

  let pred_to_sort_env = Set.Poly.map ~f:pred_to_sort_bind

  let pred_to_sort_env_map map =
    Map.rename_keys_and_drop_unused ~f:(fun p -> Some (Ident.pvar_to_tvar p))
    @@ Map.Poly.map map ~f:(fun sorts ->
           Sort.mk_fun @@ sorts @ [ T_bool.SBool ])

  let is_bool_sort = Stdlib.( = ) T_bool.SBool
  let is_int_sort = Stdlib.( = ) T_int.SInt
  let is_int_ref_sort = Stdlib.( = ) T_int.SRefInt
  let is_real_sort = Stdlib.( = ) T_real.SReal
  let is_bv_sort = function T_bv.SBV _ -> true | _ -> false
  let is_ir_sort s = is_int_sort s || is_real_sort s
  let is_irb_sort s = is_int_sort s || is_real_sort s || is_bv_sort s
  let is_dt_sort s = match s with T_dt.SDT _ -> true | _ -> false
  let is_array_sort = function T_array.SArray _ -> true | _ -> false
  let is_string_sort = Stdlib.( = ) T_string.SString
  let is_regex_sort = Stdlib.( = ) T_regex.SRegEx

  let rec occurs sv = function
    | Sort.SVar svar -> Ident.svar_equal sv svar
    | Sort.SArrow (s, c) -> occurs sv s || occurs_triple sv c
    | Sort.SPoly (svs, s) -> (not (Set.mem svs sv)) && occurs sv s
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        false
    | T_array.SArray (s1, s2) -> occurs sv s1 || occurs sv s2
    | T_tuple.STuple sorts -> List.exists sorts ~f:(occurs sv)
    | T_dt.SDT dt -> List.exists (Datatype.params_of dt (*ToDo*)) ~f:(occurs sv)
    | T_dt.SUS (_, sorts) -> List.exists sorts ~f:(occurs sv)
    | T_int.SRefInt -> false
    | T_ref.SRef sort -> occurs sv sort
    | _ -> failwith "[occurs] unknown sort"

  and occurs_cont sv = function
    | Sort.(EVar _ | Pure) -> false
    | Sort.Eff (c1, c2) -> occurs_triple sv c1 || occurs_triple sv c2
    | _ -> failwith "occurs_cont"

  and occurs_opsig sv = function
    | Sort.OpSig (opmap, _) -> List.exists (ALMap.data opmap) ~f:(occurs sv)
    | _ -> failwith "occurs_opsig"

  and occurs_triple sv c =
    occurs_opsig sv c.op_sig || occurs sv c.val_type
    || occurs_cont sv c.cont_eff

  let rec str_of_triple c =
    let open Sort in
    if Sort.is_pure c.cont_eff then
      if Sort.is_empty_closed_opsig c.op_sig then str_of_sort c.val_type
      else sprintf "(%s |> %s)" (str_of_opsig c.op_sig) (str_of_sort c.val_type)
    else if Sort.is_empty_closed_opsig c.op_sig then
      sprintf "(%s / %s)" (str_of_sort c.val_type) (str_of_cont c.cont_eff)
    else
      sprintf "(%s |> %s / %s)" (str_of_opsig c.op_sig) (str_of_sort c.val_type)
        (str_of_cont c.cont_eff)

  and str_of_sort = function
    | Sort.SVar svar -> Ident.name_of_svar svar
    | Sort.SArrow (s, c) ->
        sprintf "%s -> %s"
          ((if Sort.is_arrow s || Term.is_array_sort s then String.paren
            else Fn.id)
          @@ str_of_sort s)
          (str_of_triple c)
    | Sort.SPoly (svs, s) ->
        if Set.is_empty svs then
          failwith "[str_of_sort.SPoly]" (*str_of_sort s*)
        else if Set.is_singleton svs then
          sprintf "forall %s. %s"
            (Ident.name_of_svar @@ Set.choose_exn svs)
            (str_of_sort s)
        else
          sprintf "forall (%s). %s"
            (String.concat_map_set ~sep:"," ~f:Ident.name_of_svar svs)
            (str_of_sort s)
    | T_bool.SBool -> "bool"
    | T_int.SInt -> "int"
    | T_real.SReal -> "real"
    | T_bv.SBV size -> sprintf "bv%s" (T_bv.str_of_size size)
    | T_string.SString -> "string"
    | T_sequence.SSequence true -> "fin_sequence"
    | T_sequence.SSequence false -> "inf_sequence"
    | T_regex.SRegEx -> "regex"
    | T_array.SArray (s1, s2) ->
        sprintf "%s ->> %s"
          ((if Sort.is_arrow s1 || Term.is_array_sort s1 then String.paren
            else Fn.id)
          @@ str_of_sort s1)
          (str_of_sort s2)
    | T_tuple.STuple sorts ->
        String.paren @@ String.concat_map_list ~sep:" * " sorts ~f:str_of_sort
    | T_dt.SDT t -> (*Datatype.str_of t*) Datatype.full_name_of t
    | T_dt.SUS (name, args) ->
        if List.is_empty args then name
        else
          sprintf "%s %s"
            (String.paren
            @@ String.concat_map_list ~sep:", " args ~f:Term.str_of_sort)
            name
    | T_int.SRefInt -> "int*"
    | T_ref.SRef s -> String.paren (str_of_sort s) ^ " ref"
    | _ -> failwith "[str_of_sort] unknown sort"

  and str_of_cont = function
    | Sort.EVar evar -> Ident.name_of_evar evar
    | Sort.Pure -> "_"
    | Sort.Eff (c1, c2) ->
        sprintf "%s => %s" (str_of_triple c1) (str_of_triple c2)
    | _ -> failwith "[str_of_cont] unknown control effect"

  and str_of_opsig = function
    | Sort.OpSig (map, rho_opt) ->
        let str_map =
          String.concat_map_list (ALMap.to_alist map) ~sep:", "
            ~f:(fun (op, sort) -> sprintf "%s: %s" op (str_of_sort sort))
        in
        let str_rho =
          match rho_opt with
          | Some rvar -> " | " ^ Ident.name_of_rvar rvar
          | None -> ""
        in
        sprintf "{%s%s}" str_map str_rho
    | _ -> failwith "[str_of_opsig]"

  let rec short_name_of_sort = function
    | Sort.SVar svar -> "'" ^ Ident.name_of_svar svar
    | Sort.SArrow (s, c) ->
        sprintf "%s>%s%s%s"
          (if Sort.is_arrow s then String.paren @@ short_name_of_sort s
           else short_name_of_sort s)
          (if Sort.is_empty_opsig c.op_sig then "" else "_|>")
          (short_name_of_sort c.val_type)
          (if Sort.is_pure c.cont_eff then "" else "/_")
    | Sort.SPoly (svs, s) ->
        if Set.is_empty svs then
          failwith "[short_name_of_sort.SPoly]" (*short_name_of_sort s*)
        else
          sprintf "forall %s. %s"
            (if Set.is_singleton svs then
               Ident.name_of_svar @@ Set.choose_exn svs
             else
               String.paren
               @@ String.concat_map_set ~sep:"," ~f:Ident.name_of_svar svs)
            (short_name_of_sort s)
    | T_bool.SBool -> "b"
    | T_int.SInt -> "i"
    | T_real.SReal -> "r"
    | T_bv.SBV _ -> "bv"
    | T_string.SString -> "s"
    | T_sequence.SSequence true -> "fseq"
    | T_sequence.SSequence false -> "iseq"
    | T_regex.SRegEx -> "re"
    | T_array.SArray (s1, s2) ->
        sprintf "%s>>%s"
          (if Term.is_array_sort s1 then String.paren @@ short_name_of_sort s1
           else short_name_of_sort s1)
          (str_of_sort s2)
    | T_tuple.STuple sorts -> String.concat_map_list sorts ~f:short_name_of_sort
    | T_dt.SDT dt -> Datatype.short_name_of dt
    | T_dt.SUS (name, _) -> "us_" ^ name
    | T_int.SRefInt -> "i*"
    | T_ref.SRef sort -> "&" ^ short_name_of_sort sort
    | _ -> failwith "[short_name_of_sort] unknown sort"

  let sorts_of_sort sort =
    let rec inner visited sort =
      if Set.mem visited sort then visited
      else
        let visited' = Set.add visited sort in
        match sort with
        | T_array.SArray (s1, s2) -> inner (inner visited s1) s2
        | T_tuple.STuple sorts -> List.fold sorts ~init:visited' ~f:inner
        | T_dt.SDT dt ->
            Datatype.conses_of dt
            |> List.concat_map ~f:(Datatype.sorts_of_cons dt)
            |> List.fold ~init:visited' ~f:inner
        | T_ref.SRef sort -> inner visited' sort
        | _ -> visited'
    in
    inner Set.Poly.empty sort

  let rec svs_of_cont = function
    | Sort.(EVar _ | Pure) -> Set.Poly.empty
    | Sort.Eff (c1, c2) -> Set.union (svs_of_triple c1) (svs_of_triple c2)
    | _ -> failwith "[svs_of_cont]"

  and svs_of_sort = function
    | Sort.SVar svar -> Set.Poly.singleton svar
    | Sort.SArrow (s, c) -> Set.union (svs_of_sort s) (svs_of_triple c)
    | Sort.SPoly (svs, s) -> Set.diff (svs_of_sort s) svs
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        Set.Poly.empty
    | T_array.SArray (s1, s2) -> Set.union (svs_of_sort s1) (svs_of_sort s2)
    | T_tuple.STuple sorts ->
        Set.Poly.union_list (List.map ~f:svs_of_sort sorts)
    | T_dt.SDT dt -> Datatype.svs_of dt
    | T_dt.SUS (_, sorts) -> Set.Poly.union_list (List.map ~f:svs_of_sort sorts)
    | T_int.SRefInt -> Set.Poly.empty
    | T_ref.SRef sort -> svs_of_sort sort
    | _ -> failwith "[svs_of_sort] unknown sort"

  and svs_of_opsig = function
    | Sort.OpSig (map, _) ->
        Set.Poly.union_list @@ List.map (ALMap.data map) ~f:svs_of_sort
    | _ -> failwith "[svs_of_opsig]"

  and svs_of_triple c =
    Set.Poly.union_list
      [ svs_of_opsig c.op_sig; svs_of_sort c.val_type; svs_of_cont c.cont_eff ]

  let rec polar_svs_of_cont ~pos = function
    | Sort.(EVar _ | Pure) -> Set.Poly.empty
    | Sort.Eff (c1, c2) ->
        Set.union
          (polar_svs_of_triple ~pos:(not pos) c1)
          (polar_svs_of_triple ~pos c2)
    | _ -> failwith "[polar_svs_of_cont]"

  and polar_svs_of_sort ~pos = function
    | Sort.SVar svar -> if pos then Set.Poly.singleton svar else Set.Poly.empty
    | Sort.SArrow (s, c) ->
        Set.union
          (polar_svs_of_sort ~pos:(not pos) s)
          (polar_svs_of_triple ~pos c)
    | Sort.SPoly (svs, s) -> Set.diff (polar_svs_of_sort ~pos s) svs
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        Set.Poly.empty
    | T_array.SArray (s1, s2) ->
        Set.union
          (polar_svs_of_sort ~pos:(not pos) s1)
          (polar_svs_of_sort ~pos s2)
    | T_tuple.STuple sorts ->
        Set.Poly.union_list (List.map ~f:(polar_svs_of_sort ~pos) sorts)
    | T_dt.SDT dt -> Datatype.svs_of (*ToDo*) dt
    | T_dt.SUS (_, sorts) ->
        Set.Poly.union_list (List.map ~f:svs_of_sort (*ToDo*) sorts)
    | T_int.SRefInt -> Set.Poly.empty
    | T_ref.SRef sort -> svs_of_sort (*ToDo*) sort
    | _ -> failwith "[polar_svs_of_sort] unknown sort"

  and polar_svs_of_opsig ~pos = function
    | Sort.OpSig (map, _) ->
        Set.Poly.union_list
        @@ List.map (ALMap.data map) ~f:(polar_svs_of_sort ~pos)
    | _ -> failwith "[polar_svs_of_opsig]"

  and polar_svs_of_triple ~pos c =
    Set.Poly.union_list
      [
        polar_svs_of_opsig ~pos:(not pos) c.op_sig;
        polar_svs_of_sort ~pos c.val_type;
        polar_svs_of_cont ~pos c.cont_eff;
      ]

  let rec evs_of_cont = function
    | Sort.EVar evar -> Set.Poly.singleton evar
    | Sort.Pure -> Set.Poly.empty
    | Sort.Eff (c1, c2) -> Set.union (evs_of_triple c1) (evs_of_triple c2)
    | _ -> failwith "[evs_of_cont]"

  and evs_of_sort = function
    | Sort.SVar _ -> Set.Poly.empty
    | Sort.SArrow (s, c) -> Set.union (evs_of_sort s) (evs_of_triple c)
    | Sort.SPoly (_, s) -> evs_of_sort s
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        Set.Poly.empty
    | T_array.SArray (s1, s2) -> Set.union (evs_of_sort s1) (evs_of_sort s2)
    | T_tuple.STuple sorts ->
        Set.Poly.union_list (List.map ~f:evs_of_sort sorts)
    | T_dt.SDT dt -> Datatype.evs_of dt
    | T_dt.SUS (_, sorts) -> Set.Poly.union_list (List.map ~f:evs_of_sort sorts)
    | T_int.SRefInt -> Set.Poly.empty
    | T_ref.SRef sort -> evs_of_sort sort
    | _ -> failwith "[evs_of_sort] unknown sort"

  and evs_of_opsig = function
    | Sort.OpSig (map, _) ->
        Set.Poly.union_list @@ List.map (ALMap.data map) ~f:evs_of_sort
    | _ -> failwith "[evs_of_opsig]"

  and evs_of_triple c =
    Set.Poly.union_list
      [ evs_of_opsig c.op_sig; evs_of_sort c.val_type; evs_of_cont c.cont_eff ]

  let rec polar_evs_of_cont ~pos = function
    | Sort.EVar evar -> if pos then Set.Poly.singleton evar else Set.Poly.empty
    | Sort.Pure -> Set.Poly.empty
    | Sort.Eff (c1, c2) ->
        Set.union
          (polar_evs_of_triple ~pos:(not pos) c1)
          (polar_evs_of_triple ~pos c2)
    | _ -> failwith "[polar_evs_of_cont]"

  and polar_evs_of_sort ~pos = function
    | Sort.SVar _ -> Set.Poly.empty
    | Sort.SArrow (s, c) ->
        Set.union
          (polar_evs_of_sort ~pos:(not pos) s)
          (polar_evs_of_triple ~pos c)
    | Sort.SPoly (_, s) -> polar_evs_of_sort ~pos s
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        Set.Poly.empty
    | T_array.SArray (s1, s2) ->
        Set.union
          (polar_evs_of_sort ~pos:(not pos) s1)
          (polar_evs_of_sort ~pos s2)
    | T_tuple.STuple sorts ->
        Set.Poly.union_list (List.map ~f:(polar_evs_of_sort ~pos) sorts)
    | T_dt.SDT dt -> Datatype.evs_of (*ToDo*) dt
    | T_dt.SUS (_, sorts) ->
        Set.Poly.union_list (List.map ~f:evs_of_sort (*ToDo*) sorts)
    | T_int.SRefInt -> Set.Poly.empty
    | T_ref.SRef sort -> evs_of_sort (*ToDo*) sort
    | _ -> failwith "[polar_evs_of_sort] unknown sort"

  and polar_evs_of_opsig ~pos = function
    | Sort.OpSig (map, _) ->
        Set.Poly.union_list
        @@ List.map (ALMap.data map) ~f:(polar_evs_of_sort ~pos)
    | _ -> failwith "[polar_evs_of_opsig]"

  and polar_evs_of_triple ~pos c =
    Set.Poly.union_list
      [
        polar_evs_of_opsig ~pos:(not pos) c.op_sig;
        polar_evs_of_sort ~pos c.val_type;
        polar_evs_of_cont ~pos c.cont_eff;
      ]

  let rec rvs_of_cont = function
    | Sort.(EVar _ | Pure) -> Set.Poly.empty
    | Sort.Eff (c1, c2) -> Set.union (rvs_of_triple c1) (rvs_of_triple c2)
    | _ -> failwith "[rvs_of_cont]"

  and rvs_of_sort = function
    | Sort.SVar _ -> Set.Poly.empty
    | Sort.SArrow (s, c) -> Set.union (rvs_of_sort s) (rvs_of_triple c)
    | Sort.SPoly (_, s) -> rvs_of_sort s
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        Set.Poly.empty
    | T_array.SArray (s1, s2) -> Set.union (rvs_of_sort s1) (rvs_of_sort s2)
    | T_tuple.STuple sorts ->
        Set.Poly.union_list (List.map ~f:rvs_of_sort sorts)
    | T_dt.SDT dt -> Datatype.rvs_of dt
    | T_dt.SUS (_, sorts) -> Set.Poly.union_list (List.map ~f:rvs_of_sort sorts)
    | T_int.SRefInt -> Set.Poly.empty
    | T_ref.SRef sort -> rvs_of_sort sort
    | _ -> failwith "[rvs_of_sort] unknown sort"

  and rvs_of_opsig = function
    | Sort.OpSig (map, rv_opt) ->
        Set.Poly.union_list
        @@ (match rv_opt with
           | Some rv -> Set.Poly.singleton rv
           | None -> Set.Poly.empty)
           :: List.map (ALMap.data map) ~f:rvs_of_sort
    | _ -> failwith "[rvs_of_opsig]"

  and rvs_of_triple c =
    Set.Poly.union_list
      [ rvs_of_opsig c.op_sig; rvs_of_sort c.val_type; rvs_of_cont c.cont_eff ]

  let rec polar_rvs_of_cont ~pos = function
    | Sort.(EVar _ | Pure) -> Set.Poly.empty
    | Sort.Eff (c1, c2) ->
        Set.union
          (polar_rvs_of_triple ~pos:(not pos) c1)
          (polar_rvs_of_triple ~pos c2)
    | _ -> failwith "[polar_rvs_of_cont]"

  and polar_rvs_of_sort ~pos = function
    | Sort.SVar _ -> Set.Poly.empty
    | Sort.SArrow (s, c) ->
        Set.union
          (polar_rvs_of_sort ~pos:(not pos) s)
          (polar_rvs_of_triple ~pos c)
    | Sort.SPoly (_, s) -> polar_rvs_of_sort ~pos s
    | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
    | T_sequence.SSequence _ | T_regex.SRegEx ->
        Set.Poly.empty
    | T_array.SArray (s1, s2) ->
        Set.union
          (polar_rvs_of_sort ~pos:(not pos) s1)
          (polar_rvs_of_sort ~pos s2)
    | T_tuple.STuple sorts ->
        Set.Poly.union_list (List.map ~f:(polar_rvs_of_sort ~pos) sorts)
    | T_dt.SDT dt -> Datatype.rvs_of (*ToDo*) dt
    | T_dt.SUS (_, sorts) ->
        Set.Poly.union_list (List.map ~f:rvs_of_sort (*ToDo*) sorts)
    | T_int.SRefInt -> Set.Poly.empty
    | T_ref.SRef sort -> rvs_of_sort (*ToDo*) sort
    | _ -> failwith "[polar_rvs_of_sort] unknown sort"

  and polar_rvs_of_opsig ~pos = function
    | Sort.OpSig (map, rv_opt) ->
        Set.Poly.union_list
        @@ (match rv_opt with
           | Some rv -> if pos then Set.Poly.singleton rv else Set.Poly.empty
           | None -> Set.Poly.empty)
           :: List.map (ALMap.data map) ~f:(polar_rvs_of_sort ~pos)
    | _ -> failwith "[polar_rvs_of_opsig]"

  and polar_rvs_of_triple ~pos c =
    Set.Poly.union_list
      [
        polar_rvs_of_opsig ~pos:(not pos) c.op_sig;
        polar_rvs_of_sort ~pos c.val_type;
        polar_rvs_of_cont ~pos c.cont_eff;
      ]

  let rec subst_sorts_sort map = function
    | Sort.SVar svar -> (
        match Map.Poly.find map svar with Some s -> s | None -> Sort.SVar svar)
    | Sort.SArrow (s, c) ->
        Sort.SArrow (subst_sorts_sort map s, subst_sorts_triple map c)
    | Sort.SPoly (svs, s) ->
        Sort.SPoly (svs, subst_sorts_sort (Map.remove_keys_set map svs) s)
    (* | T_string.SString ->
       T_string.SString (*T_dt.SUS ("string", [])*)
       | T_sequence.SSequence true ->
       T_sequence.SSequence true(*T_dt.SUS ("fin_sequence", [])*)
       | T_sequence.SSequence false ->
       T_sequence.SSequence false(*T_dt.SUS ("inf_sequence", [])*) *)
    | T_array.SArray (s1, s2) ->
        T_array.SArray (subst_sorts_sort map s1, subst_sorts_sort map s2)
    | T_tuple.STuple sorts ->
        T_tuple.STuple (List.map sorts ~f:(subst_sorts_sort map))
    | T_dt.SDT dt -> T_dt.SDT (Datatype.subst_sorts map dt)
    | T_dt.SUS (name, args) ->
        T_dt.SUS (name, List.map args ~f:(subst_sorts_sort map))
    | T_ref.SRef sort -> T_ref.SRef (subst_sorts_sort map sort)
    | sort (*ToDo*) -> sort (*failwith "subst_sorts_sort"*)

  and subst_sorts_cont map = function
    | Sort.(EVar _ | Pure) as e -> e
    | Sort.Eff (c1, c2) ->
        Sort.mk_cont_eff (subst_sorts_triple map c1) (subst_sorts_triple map c2)
    | _ -> failwith "subst_sorts_cont"

  and subst_sorts_opsig map = function
    | Sort.OpSig (opmap, r) ->
        Sort.OpSig (ALMap.map opmap ~f:(subst_sorts_sort map), r)
    | _ -> failwith "subst_sorts_opsig"

  and subst_sorts_triple map c =
    {
      op_sig = subst_sorts_opsig map c.op_sig;
      val_type = subst_sorts_sort map c.val_type;
      cont_eff = subst_sorts_cont map c.cont_eff;
    }

  let rec subst_conts_sort map = function
    | Sort.SVar svar -> Sort.SVar svar
    | Sort.SArrow (s, c) ->
        Sort.SArrow (subst_conts_sort map s, subst_conts_triple map c)
    | T_array.SArray (s1, s2) ->
        T_array.SArray (subst_conts_sort map s1, subst_conts_sort map s2)
    | T_tuple.STuple sorts ->
        T_tuple.STuple (List.map sorts ~f:(subst_conts_sort map))
    | T_dt.SDT dt -> T_dt.SDT (Datatype.subst_conts map dt)
    | T_ref.SRef sort -> T_ref.SRef (subst_conts_sort map sort)
    | sort -> sort (*failwith "subst_conts_sort"*)

  and subst_conts_cont map = function
    | Sort.EVar evar -> (
        match Map.Poly.find map evar with Some e -> e | None -> Sort.EVar evar)
    | Sort.Pure -> Sort.Pure
    | Sort.Eff (c1, c2) ->
        Sort.mk_cont_eff (subst_conts_triple map c1) (subst_conts_triple map c2)
    | _ -> failwith "subst_conts_cont"

  and subst_conts_opsig map = function
    | Sort.OpSig (opmap, r) ->
        Sort.OpSig (ALMap.map opmap ~f:(subst_conts_sort map), r)
    | _ -> failwith "subst_conts_opsig"

  and subst_conts_triple map c =
    {
      op_sig = subst_conts_opsig map c.op_sig;
      val_type = subst_conts_sort map c.val_type;
      cont_eff = subst_conts_cont map c.cont_eff;
    }

  let rec subst_opsigs_sort map = function
    | Sort.SVar svar -> Sort.SVar svar
    | Sort.SArrow (s, c) ->
        Sort.SArrow (subst_opsigs_sort map s, subst_opsigs_triple map c)
    | T_array.SArray (s1, s2) ->
        T_array.SArray (subst_opsigs_sort map s1, subst_opsigs_sort map s2)
    | T_tuple.STuple sorts ->
        T_tuple.STuple (List.map sorts ~f:(subst_opsigs_sort map))
    | T_dt.SDT dt -> T_dt.SDT (Datatype.subst_opsigs map dt)
    | T_ref.SRef sort -> T_ref.SRef (subst_opsigs_sort map sort)
    | sort -> sort (*failwith "subst_opsigs_sort"*)

  and subst_opsigs_cont map = function
    | Sort.(EVar _ | Pure) as e -> e
    | Sort.Eff (c1, c2) ->
        Sort.mk_cont_eff
          (subst_opsigs_triple map c1)
          (subst_opsigs_triple map c2)
    | _ -> failwith "subst_opsigs_cont"

  and subst_opsigs_opsig map = function
    | Sort.OpSig (opmap, None) ->
        Sort.OpSig (ALMap.map opmap ~f:(subst_opsigs_sort map), None)
    | Sort.OpSig (opmap, Some rvar) -> (
        match Map.Poly.find map rvar with
        | Some (Sort.OpSig (opmap2, r_opt)) ->
            Sort.OpSig
              ( ALMap.force_merge
                  (ALMap.map opmap ~f:(subst_opsigs_sort map))
                  opmap2,
                r_opt )
        | None ->
            Sort.OpSig (ALMap.map opmap ~f:(subst_opsigs_sort map), Some rvar)
        | _ -> failwith "subst_opsigs_opsig")
    | _ -> failwith "subst_opsigs_opsig"

  and subst_opsigs_triple map c =
    {
      op_sig = subst_opsigs_opsig map c.op_sig;
      val_type = subst_opsigs_sort map c.val_type;
      cont_eff = subst_opsigs_cont map c.cont_eff;
    }

  let subst_sort (omap, smap, emap) sort =
    subst_opsigs_sort omap @@ subst_conts_sort emap
    @@ subst_sorts_sort smap sort

  let subst_cont (omap, smap, emap) eff =
    subst_opsigs_cont omap @@ subst_conts_cont emap @@ subst_sorts_cont smap eff

  let subst_opsig (omap, smap, emap) opsig =
    subst_opsigs_opsig omap @@ subst_conts_opsig emap
    @@ subst_sorts_opsig smap opsig

  let subst_triple maps c =
    Sort.
      {
        op_sig = subst_opsig maps c.op_sig;
        val_type = subst_sort maps c.val_type;
        cont_eff = subst_cont maps c.cont_eff;
      }

  let subst_all (omap, smap, emap) term =
    Term.subst_opsigs omap @@ Term.subst_conts emap
    @@ Term.subst_sorts smap term

  let rec fresh_conts_sort = function
    | Sort.SVar svar -> Sort.SVar svar
    | Sort.SArrow (s, c) ->
        Sort.SArrow
          (fresh_conts_sort s, Sort.mk_fresh_triple_from_sort c.val_type)
    | Sort.SPoly (svs, s) -> Sort.SPoly (svs, s)
    | ( T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
      | T_sequence.SSequence _ | T_regex.SRegEx ) as s ->
        s
    | T_array.SArray (s1, s2) ->
        T_array.SArray (fresh_conts_sort s1, fresh_conts_sort s2)
    | T_tuple.STuple sorts ->
        T_tuple.STuple (List.map ~f:fresh_conts_sort sorts)
    | T_dt.SDT dt -> T_dt.SDT (Datatype.fresh_conts_sort dt)
    | T_dt.SUS (name, sorts) ->
        T_dt.SUS (name, List.map ~f:fresh_conts_sort sorts)
    | T_int.SRefInt -> T_int.SRefInt
    | T_ref.SRef sort -> T_ref.SRef (fresh_conts_sort sort)
    | _ -> failwith "[fresh_conts_sort] unknown sort"

  let rec fresh_rvs_cont = function
    | Sort.(EVar _ | Pure) as e -> e
    | Sort.Eff (c1, c2) ->
        Sort.mk_cont_eff (fresh_rvs_triple c1) (fresh_rvs_triple c2)
    | _ -> failwith "fresh_rvs_cont"

  and fresh_rvs_sort = function
    | Sort.SVar _ as s -> s
    | Sort.SArrow (s, c) -> Sort.SArrow (fresh_rvs_sort s, fresh_rvs_triple c)
    | Sort.SPoly (svs, s) -> Sort.SPoly (svs, fresh_rvs_sort s)
    | ( T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
      | T_sequence.SSequence _ | T_regex.SRegEx ) as s ->
        s
    | T_array.SArray (s1, s2) ->
        T_array.SArray (fresh_rvs_sort s1, fresh_rvs_sort s2)
    | T_tuple.STuple sorts -> T_tuple.STuple (List.map ~f:fresh_rvs_sort sorts)
    | T_dt.SDT dt -> T_dt.SDT (Datatype.fresh_rvs_sort dt)
    | T_dt.SUS (name, sorts) -> T_dt.SUS (name, List.map ~f:fresh_rvs_sort sorts)
    | T_int.SRefInt -> T_int.SRefInt
    | T_ref.SRef sort -> T_ref.SRef (fresh_rvs_sort sort)
    | _ -> failwith "[fresh_rvs_sort] unknown sort"

  and fresh_rvs_opsig = function
    | Sort.OpSig (map, _) ->
        Sort.OpSig
          (ALMap.map map ~f:fresh_rvs_sort, Some (Ident.mk_fresh_rvar ()))
    | _ -> failwith "fresh_rvs_opsig"

  and fresh_rvs_triple c =
    {
      op_sig = fresh_rvs_opsig c.op_sig;
      val_type = fresh_rvs_sort c.val_type;
      cont_eff = fresh_rvs_cont c.cont_eff;
    }

  let rec pat_match_sort sort1 sort2 =
    if Stdlib.(sort1 = sort2) then
      (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)
    else
      match (sort1, sort2) with
      | Sort.SVar svar, sort | sort, Sort.SVar svar (*ToDo*) ->
          (Map.Poly.empty, Map.Poly.singleton svar sort, Map.Poly.empty)
      | Sort.SArrow (s1, c1), Sort.SArrow (s2, c2) ->
          let omap1, smap1, emap1 = pat_match_sort s1 s2 in
          let omap2, smap2, emap2 = pat_match_triple c1 c2 in
          ( Map.force_merge omap1 omap2,
            Map.force_merge smap1 smap2,
            Map.force_merge emap1 emap2 )
      | Sort.SPoly (svs1, s1), Sort.SPoly (svs2, s2) when Set.equal svs1 svs2 ->
          pat_match_sort s1 s2
      | T_array.SArray (s11, s12), T_array.SArray (s21, s22) ->
          let omaps, smaps, emaps =
            List.unzip3
            @@ List.map2_exn [ s11; s12 ] [ s21; s22 ] ~f:pat_match_sort
          in
          ( Map.force_merge_list omaps,
            Map.force_merge_list smaps,
            Map.force_merge_list emaps )
      | T_tuple.STuple sorts1, T_tuple.STuple sorts2 ->
          let omaps, smaps, emaps =
            List.unzip3 @@ List.map2_exn sorts1 sorts2 ~f:pat_match_sort
          in
          ( Map.force_merge_list omaps,
            Map.force_merge_list smaps,
            Map.force_merge_list emaps )
      | T_dt.SDT dt1, T_dt.SDT dt2 -> Datatype.pat_match_sort dt1 dt2
      | T_dt.SUS (name1, sorts1), T_dt.SUS (name2, sorts2)
        when String.(name1 = name2) ->
          let omaps, smaps, emaps =
            List.unzip3 @@ List.map2_exn sorts1 sorts2 ~f:pat_match_sort
          in
          ( Map.force_merge_list omaps,
            Map.force_merge_list smaps,
            Map.force_merge_list emaps )
      | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) when String.(dt1.name = name2) ->
          let omaps, smaps, emaps =
            List.unzip3
            @@ List.map2_exn (Datatype.params_of dt1) sorts2 ~f:pat_match_sort
          in
          ( Map.force_merge_list omaps,
            Map.force_merge_list smaps,
            Map.force_merge_list emaps )
      | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 when String.(name1 = dt2.name) ->
          let omaps, smaps, emaps =
            List.unzip3
            @@ List.map2_exn sorts1 (Datatype.params_of dt2) ~f:pat_match_sort
          in
          ( Map.force_merge_list omaps,
            Map.force_merge_list smaps,
            Map.force_merge_list emaps )
      | T_ref.SRef sort1, T_ref.SRef sort2 -> pat_match_sort sort1 sort2
      | _ ->
          failwith
            (sprintf "[pat_match_sort] %s and %s does not match"
               (str_of_sort sort1) (str_of_sort sort2))

  and pat_match_cont e1 e2 =
    if Stdlib.(e1 = e2) then (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)
    else
      match (e1, e2) with
      | Sort.EVar evar, _ ->
          (Map.Poly.empty, Map.Poly.empty, Map.Poly.singleton evar e2)
      | Sort.Eff (c11, c12), Sort.Eff (c21, c22) ->
          let omap1, smap1, emap1 = pat_match_triple c11 c21 in
          let omap2, smap2, emap2 = pat_match_triple c12 c22 in
          ( Map.force_merge omap1 omap2,
            Map.force_merge smap1 smap2,
            Map.force_merge emap1 emap2 )
      | _ -> failwith "pat_match_cont"

  and pat_match_opsig o1 o2 =
    if Stdlib.(o1 = o2) then (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)
    else
      match (o1, o2) with
      | Sort.OpSig (map1, r1), Sort.OpSig (map2, r2) ->
          let lefts, boths, rights = ALMap.split_lbr map1 map2 in
          if List.is_empty lefts && List.is_empty rights then
            (*ToDo*)
            let omap =
              match (r1, r2) with
              | None, None -> Map.Poly.empty
              | Some r1, Some r2 ->
                  if Stdlib.(r1 = r2) (*ToDo*) then Map.Poly.empty
                  else
                    Map.Poly.singleton r1
                      (Sort.mk_empty_open_opsig_from_rvar r2) (*ToDo*)
              (*failwith @@ sprintf "[pat_match_opsig @ 1] %s and %s"
                (Ident.name_of_rvar r1) (Ident.name_of_rvar r2)*)
              | Some r, None ->
                  Map.Poly.singleton r Sort.empty_closed_opsig (*ToDo*)
              (*failwith @@ sprintf "[pat_match_opsig @ 2] %s" (Ident.name_of_rvar r)*)
              | None, Some r ->
                  failwith
                  @@ sprintf "[pat_match_opsig @ 3] %s" (Ident.name_of_rvar r)
            in
            let omaps, smaps, emaps =
              List.unzip3 @@ List.map boths ~f:(snd >> uncurry pat_match_sort)
            in
            ( Map.force_merge_list (omap :: omaps),
              Map.force_merge_list smaps,
              Map.force_merge_list emaps )
          else failwith "[pat_match_opsig @ 4]"
      | _ -> failwith "[pat_match_opsig @ 5]"

  and pat_match_triple c1 c2 =
    let omap1, smap1, emap1 =
      pat_match_opsig c1.op_sig c2.op_sig
      (*ToDo*)
    in
    let omap2, smap2, emap2 = pat_match_sort c1.val_type c2.val_type in
    let omap3, smap3, emap3 = pat_match_cont c1.cont_eff c2.cont_eff in
    ( Map.force_merge_list [ omap1; omap2; omap3 ],
      Map.force_merge_list [ smap1; smap2; smap3 ],
      Map.force_merge_list [ emap1; emap2; emap3 ] )

  (** Construction *)

  let mk_var ?(info = Dummy) var sort = Var (var, sort, info)
  let mk_fresh_var = mk_var (Ident.mk_fresh_tvar ())
  let mk_fsym_app ?(info = Dummy) sym ts = FunApp (sym, ts, info)

  let mk_fvar_app ?(info = Dummy) tvar sargs sret ts =
    FunApp (FVar (tvar, sargs, sret), ts, info)

  let fvar_app_of_senv ?(info = Dummy) tvar senv sort =
    mk_fvar_app ~info tvar (List.map ~f:snd senv) sort (Term.of_sort_env senv)

  let mk_let_term ?(info = Dummy) tvar sort def body =
    LetTerm (tvar, sort, def, body, info)

  let rec mk_dummy = function
    | Sort.SVar (Ident.Svar name) as sort ->
        let name = (*ToDo*) "dummy_" ^ name in
        add_dummy_term (Ident.Tvar name) sort;
        Term.mk_var (Ident.Tvar name) sort
    | Sort.SArrow _ as sort ->
        let name = sprintf "dummy_arrow(%s)" (Term.str_of_sort sort) in
        add_dummy_term (Ident.Tvar name) sort;
        Term.mk_var (Ident.Tvar name) sort
    | T_bool.SBool -> T_bool.mk_false ()
    | T_int.SInt -> T_int.zero ()
    | T_real.SReal -> T_real.rzero ()
    | T_bv.SBV size -> T_bv.bvzero ~size ()
    | T_string.SString -> mk_fsym_app (T_string.StrConst "") []
    | T_sequence.SSequence true -> T_sequence.mk_eps ()
    | T_sequence.SSequence false ->
        failwith "[mk_dummy] 'SSequence false' not supported"
    | T_regex.SRegEx -> T_regex.mk_empty ()
    | T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 @@ mk_dummy s2
    | T_tuple.STuple sorts ->
        T_tuple.mk_tuple_cons sorts @@ List.map ~f:mk_dummy sorts
    | (T_dt.SDT _ | T_dt.SUS (_, _)) as sort -> T_dt.mk_dummy sort
    | T_int.SRefInt -> failwith "[mk_dummy] 'SRefInt' not supported"
    | T_ref.SRef sort -> T_ref.mk_ref sort @@ mk_dummy sort
    | s -> failwith @@ "[mk_dummy] not supported: " ^ str_of_sort s

  let rec of_value dtenv = function
    | Value.Bool b -> T_bool.of_atom @@ Atom.mk_bool b
    | Value.Int i -> T_int.mk_int i
    | Value.Real r -> T_real.mk_real r
    | Value.BV (size, bits) -> T_bv.mk_bvnum ~size bits
    | Value.Arr (dummy, v, m) ->
        let default = of_value dtenv v in
        let elem_sort = Term.sort_of default in
        let index_sort =
          match Map.Poly.keys m with
          | [] -> Term.sort_of @@ of_value dtenv dummy
          | v :: _ -> Term.sort_of @@ of_value dtenv v
        in
        Map.Poly.fold m
          ~init:(T_array.mk_const_array index_sort elem_sort default)
          ~f:(fun ~key ~data acc ->
            let key = of_value dtenv key in
            let data = of_value dtenv data in
            T_array.mk_store index_sort elem_sort acc key data)
    | Value.TupleCons vs ->
        let ts = List.map vs ~f:(of_value dtenv) in
        T_tuple.mk_tuple_cons (List.map ts ~f:Term.sort_of) ts
    | Value.DTCons (name, pvs, vs) ->
        let t =
          Datatype.update_params
            (Option.value_exn (DTEnv.look_up_dt_by_cons_name dtenv name))
            (List.map pvs ~f:(of_value dtenv >> Term.sort_of))
        in
        T_dt.mk_cons t name (List.map vs ~f:(of_value dtenv))

  let of_sort_env = List.map ~f:(uncurry mk_var)

  (** Destruction *)

  let let_var = function
    | Var (var, sort, info) -> ((var, sort), info)
    | FunApp
        ( T_bool.Formula
            (Formula.Atom
               (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _)),
          _,
          info ) ->
        ((Ident.Tvar var, T_bool.SBool), info)
    | _ -> assert false

  let let_app = function
    | FunApp (sym, ts, info) -> (sym, ts, info)
    | _ -> assert false

  let let_fvar_app = function
    | FunApp (FVar (var, sargs, sret), ts, info) -> (var, sargs, sret, ts, info)
    | _ -> assert false

  let let_funcall = function
    | FunApp (FunCall funname, ts, info) -> (funname, ts, info)
    | _ -> assert false

  let let_let_term = function
    | LetTerm (var, sort, def, body, info) -> (var, sort, def, body, info)
    | _ -> assert false

  (** Function Symbols *)

  let is_fvar_sym = function FVar (_, _, _) -> true | _ -> false

  let str_of_funsym = function
    | FVar (x, _, _) -> Ident.name_of_tvar x
    | T_bool.Formula phi -> sprintf "Formula(%s)" @@ Formula.str_of phi
    | T_bool.IfThenElse -> "ite"
    | T_int.Int n -> Z.to_string n
    | T_int.Neg -> "-"
    | T_int.Nop -> "nop"
    | T_int.Abs -> "abs"
    | T_int.Add -> "+"
    | T_int.Sub -> "-"
    | T_int.Mul -> "*"
    | T_int.Div Euclidean -> "ediv"
    | T_int.Div _ -> "div"
    | T_int.Rem Euclidean -> "erem"
    | T_int.Rem _ -> "rem"
    | T_int.Power -> "^"
    | T_real.Real r -> Q.to_string r
    | T_real.Alge n -> "alge@" ^ string_of_int n
    | T_real.RNeg -> "-."
    | T_real.RAbs -> "abs."
    | T_real.RAdd -> "+."
    | T_real.RSub -> "-."
    | T_real.RMul -> "*."
    | T_real.RDiv -> "/."
    | T_real.RPower -> "^."
    | T_bv.BVNum (_size, n) -> Z.to_string n
    | T_bv.BVNot size -> sprintf "not%s" (T_bv.str_of_size size)
    | T_bv.BVAnd size -> sprintf "and%s" (T_bv.str_of_size size)
    | T_bv.BVOr size -> sprintf "or%s" (T_bv.str_of_size size)
    | T_bv.BVXor size -> sprintf "xor%s" (T_bv.str_of_size size)
    | T_bv.BVNand size -> sprintf "nand%s" (T_bv.str_of_size size)
    | T_bv.BVNor size -> sprintf "nor%s" (T_bv.str_of_size size)
    | T_bv.BVXnor size -> sprintf "xnor%s" (T_bv.str_of_size size)
    | T_bv.BVNeg size -> sprintf "neg%s" (T_bv.str_of_size size)
    | T_bv.BVAdd size -> sprintf "add%s" (T_bv.str_of_size size)
    | T_bv.BVSub size -> sprintf "sub%s" (T_bv.str_of_size size)
    | T_bv.BVMul size -> sprintf "mul%s" (T_bv.str_of_size size)
    | T_bv.BVDiv (size, signed) ->
        sprintf "%sdiv%s" (T_bv.str_of_signed signed) (T_bv.str_of_size size)
    | T_bv.BVRem (size, signed) ->
        sprintf "%srem%s" (T_bv.str_of_signed signed) (T_bv.str_of_size size)
    | T_bv.BVSMod size -> sprintf "smod%s" (T_bv.str_of_size size)
    | T_bv.BVSHL size -> sprintf "shl%s" (T_bv.str_of_size size)
    | T_bv.BVLSHR size -> sprintf "lshr%s" (T_bv.str_of_size size)
    | T_bv.BVASHR size -> sprintf "ashr%s" (T_bv.str_of_size size)
    | T_bv.BVEXTRACT (size, h, l) ->
        sprintf "extract%s[%d:%d]" (T_bv.str_of_size size) h l
    | T_bv.BVSEXT (size, ext) -> sprintf "sext%s+%d" (T_bv.str_of_size size) ext
    | T_bv.BVZEXT (size, ext) -> sprintf "zext%s+%d" (T_bv.str_of_size size) ext
    | T_bv.BVCONCAT (size1, size2) ->
        sprintf "concat%s,%s" (T_bv.str_of_size size1) (T_bv.str_of_size size2)
    | T_irb.IntToReal -> "int_to_real"
    | T_irb.RealToInt -> "real_to_int"
    | T_irb.IntToBV size -> sprintf "int_to_bv%s" (T_bv.str_of_size size)
    | T_irb.BVToInt (size, signed) ->
        sprintf "bv_to_%sint%s"
          (T_bv.str_of_signed signed)
          (T_bv.str_of_size size)
    | T_num.Value (v, svar) ->
        sprintf "value(%s:%s)" v (Ident.name_of_svar svar)
    | T_num.NNeg svar ->
        if true then "'-" else sprintf "-_%s" (Ident.name_of_svar svar)
    | T_num.NSEXT (size, svar1, ext, svar2) ->
        if true then "'sext"
        else
          sprintf "sext%s+%d:%s->%s" (T_bv.str_of_size size) ext
            (Ident.name_of_svar svar1) (Ident.name_of_svar svar2)
    | T_num.NAdd svar ->
        if true then "'+" else sprintf "+_%s" (Ident.name_of_svar svar)
    | T_num.NSub svar ->
        if true then "'-" else sprintf "-_%s" (Ident.name_of_svar svar)
    | T_num.NMul svar ->
        if true then "'*" else sprintf "*_%s" (Ident.name_of_svar svar)
    | T_num.NDiv (svar, _m) ->
        if true then "'/" else sprintf "/_%s" (Ident.name_of_svar svar)
    | T_num.NRem (svar, _m) ->
        if true then "'rem" else sprintf "rem_%s" (Ident.name_of_svar svar)
    | T_num.NPower svar ->
        if true then "'^" else sprintf "^_%s" (Ident.name_of_svar svar)
    | T_string.StrConst str -> sprintf "\"%s\"" str
    | T_sequence.SeqEpsilon -> "eps"
    | T_sequence.SeqSymbol ev -> ev
    | T_sequence.SeqConcat fin ->
        sprintf "concat_%s" (if fin then "fin" else "inf")
    | T_sequence.SeqLeftQuotient fin ->
        sprintf "left_quot_%s" (if fin then "fin" else "inf")
    | T_sequence.SeqRightQuotient fin ->
        sprintf "right_quot_%s" (if fin then "fin" else "inf")
    | T_regex.RegEmpty -> "empty"
    | T_regex.RegFull -> "full"
    | T_regex.RegEpsilon -> "eps"
    | T_regex.RegStr -> "str_to_re"
    | T_regex.RegComplement -> "complement"
    | T_regex.RegStar -> "star"
    | T_regex.RegPlus -> "plus"
    | T_regex.RegOpt -> "opt"
    | T_regex.RegConcat -> "concat"
    | T_regex.RegUnion -> "union"
    | T_regex.RegInter -> "inter"
    | T_array.AConst (s1, s2) ->
        if true then "const"
        else sprintf "const_array[%s>>%s]" (str_of_sort s1) (str_of_sort s2)
    | T_array.AStore _ -> "store"
    | T_array.ASelect _ -> "select"
    | T_tuple.TupleCons _ -> "t_cons"
    | T_tuple.TupleSel (_, i) -> sprintf "t_sel.%d" i
    | T_dt.DTCons (name, args, dt) ->
        if true then sprintf "%s" name
        else
          sprintf "[%s:%s]" name
            (List.fold_left args ~init:(short_name_of_sort @@ T_dt.SDT dt)
               ~f:(fun ret arg -> short_name_of_sort arg ^ "->" ^ ret))
    | T_dt.DTSel (name, dt, ret_sort) ->
        if true then sprintf "%s" name
        else
          sprintf "[%s:%s -> %s]" name
            (short_name_of_sort @@ T_dt.SDT dt)
            (short_name_of_sort ret_sort)
    | T_ref.Ref sort -> sprintf "ref(%s)" (short_name_of_sort sort)
    | T_ref.Deref sort -> sprintf "deref(%s)" (short_name_of_sort sort)
    | T_ref.Update sort -> sprintf "update(%s)" (short_name_of_sort sort)
    | _ -> failwith "[str_of_funsym] unknown function symbol"

  let rename_fun_sym map = function
    | FVar (var', sargs, sret) as fsym -> (
        match Map.Poly.find map var' with
        | None -> fsym
        | Some var -> FVar (var, sargs, sret))
    | T_bool.Formula phi -> T_bool.Formula (Formula.rename map phi)
    | fsym -> fsym

  let rename_pvars_fun_sym map = function
    | T_bool.Formula phi -> T_bool.Formula (Formula.rename_pvars map phi)
    | fsym -> fsym

  let rename_sorted_pvars_fun_sym map = function
    | T_bool.Formula phi -> T_bool.Formula (Formula.rename_sorted_pvars map phi)
    | fsym -> fsym

  let alpha_rename_let_fun_sym ?(map = Map.Poly.empty) = function
    | T_bool.Formula phi -> T_bool.Formula (Formula.alpha_rename_let ~map phi)
    | FVar (var, sargs, sret) as fsym -> (
        match Map.Poly.find map var with
        | Some v -> FVar (v, sargs, sret)
        | None -> fsym)
    | fsym -> fsym

  let subst_fun_sym str_of map = function
    | FVar (var', sargs, sret) as fsym -> (
        match Map.Poly.find map var' with
        | None -> fsym
        | Some t -> (
            try FVar (fst @@ fst @@ let_var t, sargs, sret)
            with _ ->
              failwith
              @@ sprintf "[subst_fun_sym] %s |-> %s" (Ident.name_of_tvar var')
                   (str_of t)))
    | T_bool.Formula phi -> T_bool.Formula (Formula.subst map phi)
    | fsym -> fsym

  let subst_sorts_fun_sym map = function
    | FVar (var, sargs, sret) ->
        FVar
          ( var,
            List.map ~f:(Term.subst_sorts_sort map) sargs,
            Term.subst_sorts_sort map sret )
    | T_num.(
        ( Value (_, svar)
        | NNeg svar
        | NAdd svar
        | NSub svar
        | NMul svar
        | NDiv (svar, _)
        | NRem (svar, _)
        | NPower svar )) as fsym ->
        T_num.fsym_of_num_fsym fsym
          [ Term.subst_sorts_sort map @@ Sort.SVar svar ]
    | T_num.NSEXT (_, svar1, _, svar2) as fsym ->
        T_num.fsym_of_num_fsym fsym
          [
            Term.subst_sorts_sort map @@ Sort.SVar svar1;
            Term.subst_sorts_sort map @@ Sort.SVar svar2;
          ]
    | T_bool.Formula phi -> T_bool.Formula (Formula.subst_sorts map phi)
    | T_array.AConst (s1, s2) ->
        T_array.AConst
          (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
    | T_array.AStore (s1, s2) ->
        T_array.AStore
          (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
    | T_array.ASelect (s1, s2) ->
        T_array.ASelect
          (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
    | T_tuple.TupleCons sorts ->
        T_tuple.TupleCons (List.map ~f:(Term.subst_sorts_sort map) sorts)
    | T_tuple.TupleSel (sorts, i) ->
        T_tuple.TupleSel (List.map ~f:(Term.subst_sorts_sort map) sorts, i)
    | T_dt.DTCons (name, arg_sorts, dt) ->
        T_dt.DTCons
          ( name,
            List.map arg_sorts ~f:(Term.subst_sorts_sort map),
            Datatype.subst_sorts map dt )
    | T_dt.DTSel (name, dt, sort) ->
        T_dt.DTSel
          (name, Datatype.subst_sorts map dt, Term.subst_sorts_sort map sort)
    | fsym -> fsym (* ToDo *)

  let subst_conts_fun_sym map = function
    | FVar (var, sargs, sret) ->
        FVar
          ( var,
            List.map sargs ~f:(Term.subst_conts_sort map),
            Term.subst_conts_sort map sret )
    | T_bool.Formula phi -> T_bool.Formula (Formula.subst_conts map phi)
    | T_num.(
        ( Value (_, svar)
        | NNeg svar
        | NAdd svar
        | NSub svar
        | NMul svar
        | NDiv (svar, _)
        | NRem (svar, _)
        | NPower svar )) as fsym ->
        T_num.fsym_of_num_fsym fsym
          [ Term.subst_conts_sort map @@ Sort.SVar svar ]
    | T_num.NSEXT (_, svar1, _, svar2) as fsym ->
        T_num.fsym_of_num_fsym fsym
          [
            Term.subst_conts_sort map @@ Sort.SVar svar1;
            Term.subst_conts_sort map @@ Sort.SVar svar2;
          ]
    | T_array.AConst (s1, s2) ->
        T_array.AConst
          (Term.subst_conts_sort map s1, Term.subst_conts_sort map s2)
    | T_array.AStore (s1, s2) ->
        T_array.AStore
          (Term.subst_conts_sort map s1, Term.subst_conts_sort map s2)
    | T_array.ASelect (s1, s2) ->
        T_array.ASelect
          (Term.subst_conts_sort map s1, Term.subst_conts_sort map s2)
    | T_tuple.TupleCons sorts ->
        T_tuple.TupleCons (List.map sorts ~f:(Term.subst_conts_sort map))
    | T_tuple.TupleSel (sorts, i) ->
        T_tuple.TupleSel (List.map sorts ~f:(Term.subst_conts_sort map), i)
    | T_dt.DTCons (name, arg_sorts, dt) ->
        T_dt.DTCons
          ( name,
            List.map arg_sorts ~f:(Term.subst_conts_sort map),
            Datatype.subst_conts map dt )
    | T_dt.DTSel (name, dt, sort) ->
        T_dt.DTSel
          (name, Datatype.subst_conts map dt, Term.subst_conts_sort map sort)
    | fsym -> fsym (* ToDo *)

  let subst_opsigs_fun_sym map = function
    | FVar (var, sargs, sret) ->
        FVar
          ( var,
            List.map sargs ~f:(Term.subst_opsigs_sort map),
            Term.subst_opsigs_sort map sret )
    | T_bool.Formula phi -> T_bool.Formula (Formula.subst_opsigs map phi)
    | T_num.(
        ( Value (_, svar)
        | NNeg svar
        | NAdd svar
        | NSub svar
        | NMul svar
        | NDiv (svar, _)
        | NRem (svar, _)
        | NPower svar )) as fsym ->
        T_num.fsym_of_num_fsym fsym
          [ Term.subst_opsigs_sort map @@ Sort.SVar svar ]
    | T_num.NSEXT (_, svar1, _, svar2) as fsym ->
        T_num.fsym_of_num_fsym fsym
          [
            Term.subst_opsigs_sort map @@ Sort.SVar svar1;
            Term.subst_opsigs_sort map @@ Sort.SVar svar2;
          ]
    | T_array.AConst (s1, s2) ->
        T_array.AConst
          (Term.subst_opsigs_sort map s1, Term.subst_opsigs_sort map s2)
    | T_array.AStore (s1, s2) ->
        T_array.AStore
          (Term.subst_opsigs_sort map s1, Term.subst_opsigs_sort map s2)
    | T_array.ASelect (s1, s2) ->
        T_array.ASelect
          (Term.subst_opsigs_sort map s1, Term.subst_opsigs_sort map s2)
    | T_tuple.TupleCons sorts ->
        T_tuple.TupleCons (List.map sorts ~f:(Term.subst_opsigs_sort map))
    | T_tuple.TupleSel (sorts, i) ->
        T_tuple.TupleSel (List.map sorts ~f:(Term.subst_opsigs_sort map), i)
    | T_dt.DTCons (name, arg_sorts, dt) ->
        T_dt.DTCons
          ( name,
            List.map arg_sorts ~f:(Term.subst_opsigs_sort map),
            Datatype.subst_opsigs map dt )
    | T_dt.DTSel (name, dt, sort) ->
        T_dt.DTSel
          (name, Datatype.subst_opsigs map dt, Term.subst_opsigs_sort map sort)
    | T_ref.Ref sort -> T_ref.Ref (Term.subst_opsigs_sort map sort)
    | T_ref.Deref sort -> T_ref.Deref (Term.subst_opsigs_sort map sort)
    | T_ref.Update sort -> T_ref.Update (Term.subst_opsigs_sort map sort)
    | fsym -> fsym (* ToDo *)

  let negate_fsym = function
    | T_int.Add -> T_int.Sub
    | T_int.Sub -> T_int.Add
    | T_real.RAdd -> T_real.RSub
    | T_real.RSub -> T_real.RAdd
    | fsym ->
        failwith @@ sprintf "[T_int.negate_fsym] %s" (Term.str_of_funsym fsym)

  (** Morphism *)

  let rec para ~f = function
    | Var (tvar, sort, _) -> f#fvar tvar sort
    | FunApp (fsym (*ToDo: can be formula*), args, _) ->
        f#fapp fsym (args, List.map args ~f:(para ~f))
    | LetTerm (tvar, sort, def, body, _) ->
        f#flet tvar sort (def, para ~f def) (body, para ~f body)

  let rec fold ~f = function
    | Var (tvar, sort, _) -> f#fvar tvar sort
    | FunApp (fsym (*ToDo: can be formula*), args, _) ->
        f#fapp fsym @@ List.map args ~f:(fold ~f)
    | LetTerm (tvar, sort, def, body, _) ->
        f#flet tvar sort (fold ~f def) (fold ~f body)

  let map_term _ ~f =
    fold
      ~f:
        (object
           method fvar tvar sort = f @@ Term.mk_var tvar sort

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] ->
                 f
                 @@ Term.mk_fsym_app
                      (T_bool.Formula (Formula.map_term ~f phi))
                      args
             | _, _ -> f @@ Term.mk_fsym_app fsym args

           method flet tvar sort def body =
             f @@ Term.mk_let_term tvar sort def body
        end)

  let iter_term ~f t =
    ignore
    @@ map_term true t ~f:(fun t ->
           f t;
           t);
    ()

  let map_atom ~f =
    fold
      ~f:
        (object
           method fvar tvar sort = Term.mk_var tvar sort

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] ->
                 Term.mk_fsym_app (T_bool.Formula (Formula.map_atom ~f phi)) []
             | _, _ -> Term.mk_fsym_app fsym args

           method flet tvar sort def body = Term.mk_let_term tvar sort def body
        end)

  let map_atom_polarity ~f =
    fold
      ~f:
        (object
           method fvar tvar sort _polarity = Term.mk_var tvar sort

           method fapp fsym args polarity =
             match (fsym, args) with
             | T_bool.Formula phi, [] ->
                 Term.mk_fsym_app
                   (T_bool.Formula (Formula.map_atom_polarity ~f phi polarity))
                   []
             | _, _ ->
                 Term.mk_fsym_app fsym
                   (List.map args ~f:(fun arg -> arg polarity))

           method flet tvar sort def body polarity =
             Term.mk_let_term tvar sort (def polarity) (body polarity)
        end)

  let iter_atom ~f t =
    ignore
    @@ map_atom t ~f:(fun atm ->
           f atm;
           Formula.mk_atom atm);
    ()

  (** Printing *)

  let rec str_of ?(priority = Priority.lowest) t0 =
    para
      ~f:
        (object
           method fvar tvar sort _priority =
             match sort with
             | T_int.SRefInt -> "&" ^ Ident.name_of_tvar tvar
             | T_int.SUnrefInt -> "*" ^ Ident.name_of_tvar tvar
             | sort ->
                 if true then Ident.name_of_tvar tvar
                 else
                   sprintf "%s:%s" (Ident.name_of_tvar tvar)
                     (short_name_of_sort sort)

           method fapp fsym (ts, args) priority =
             match (fsym, args) with
             | FVar (x, _, _), [] -> Ident.name_of_tvar x
             | FVar (x, _, _), ts ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "\\%s %s" (Ident.name_of_tvar x)
                 @@ String.concat_map_list ~sep:" " ts ~f:(fun t ->
                        t (Priority.fun_app + 1))
             | T_bool.Formula phi, [] ->
                 Priority.add_paren priority Priority.lowest
                 (*ToDo*) @@ String.angle_bracket
                 @@ Formula.str_of ~priority:Priority.lowest phi
             | T_bool.IfThenElse, [ cond; then_; else_ ] ->
                 Priority.add_paren priority Priority.ite
                 @@ sprintf "if %s then %s else %s"
                      (cond Priority.ite (*ToDo*))
                      (then_ Priority.lowest (*ToDo*))
                      (else_ Priority.ite (*ToDo*))
             | T_int.Int n, [] ->
                 if Z.Compare.(n < Z.zero) then
                   Priority.add_paren priority Priority.neg_deref
                   @@ sprintf "-%s" (Z.to_string @@ Z.neg n)
                 else Z.to_string n
             | T_real.Real r, [] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ "real" ^ String.paren @@ Q.to_string r
             | T_real.Alge n, [ t ] ->
                 sprintf "root-obj(%s, %s)" (t Priority.lowest)
                   (string_of_int n)
             | T_bv.BVNum (size, n), [] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s0b%s"
                      (if Option.is_none size then "?" else "")
                      (z_to_bin_string_fixed (T_bv.bits_of size) n)
             | T_num.Value _, _ -> str_of_funsym fsym
             | ( ( T_int.(Nop | Abs)
                 | T_real.RAbs
                 | T_bv.(BVNot _ | BVNeg _ | BVEXTRACT _ | BVSEXT _ | BVZEXT _)
                 | T_irb.(IntToReal | RealToInt | IntToBV _ | BVToInt _)
                 | T_num.NSEXT _ ),
                 [ t ] ) ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s" (str_of_funsym fsym)
                      (t (Priority.fun_app + 1))
             | (T_int.Neg | T_real.RNeg | T_num.NNeg _), [ t ] ->
                 Priority.add_paren priority Priority.neg_deref
                 @@ sprintf "%s%s" (str_of_funsym fsym)
                      (t (Priority.neg_deref + 1))
             | ( ( T_int.(Add | Sub)
                 | T_real.(RAdd | RSub)
                 | T_bv.(BVAdd _ | BVSub _)
                 | T_num.(NAdd _ | NSub _) ),
                 [ t1; t2 ] ) ->
                 Priority.add_paren priority Priority.add_sub
                 @@ sprintf "%s %s %s" (t1 Priority.add_sub)
                      (str_of_funsym fsym)
                      (t2 (Priority.add_sub + 1))
             | ( ( T_int.(Mul | Div _ | Rem _)
                 | T_real.(RMul | RDiv)
                 | T_bv.(BVMul _ | BVDiv _ | BVRem _ | BVSMod _)
                 | T_num.(NMul _ | NDiv _ | NRem _) ),
                 [ t1; t2 ] ) ->
                 Priority.add_paren priority Priority.mul_div_mod
                 @@ sprintf "%s %s %s" (t1 Priority.mul_div_mod)
                      (str_of_funsym fsym)
                      (t2 (Priority.mul_div_mod + 1))
             | (T_int.Power | T_real.RPower | T_num.NPower _), [ t1; t2 ] ->
                 Priority.add_paren priority Priority.append_power
                 @@ sprintf "%s %s %s"
                      (t1 (Priority.append_power + 1))
                      (str_of_funsym fsym) (t2 Priority.append_power)
             | ( T_bv.(
                   ( BVAnd _ | BVOr _ | BVXor _ | BVNand _ | BVNor _ | BVXnor _
                   | BVSHL _ | BVLSHR _ | BVASHR _ | BVCONCAT _ )),
                 [ t1; t2 ] ) ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
                      (t2 (Priority.fun_app + 1))
             | ( ( T_int.(Add | Sub | Mul | Div _ | Rem _ | Power)
                 | T_real.(RAdd | RSub | RMul | RDiv | RPower)
                 | T_bv.(
                     ( BVAnd _ | BVOr _ | BVXor _ | BVNand _ | BVNor _
                     | BVXnor _ | BVAdd _ | BVSub _ | BVMul _ | BVDiv _
                     | BVRem _ | BVSMod _ | BVSHL _ | BVLSHR _ | BVASHR _ ))
                 | T_num.(NAdd _ | NSub _ | NMul _ | NDiv _ | NRem _ | NPower _)
                   ),
                 _ ) ->
                 failwith
                   "add, sub, mul, div, mod, rem, power, bitwise operators are \
                    binary"
             | T_string.StrConst _, [] -> str_of_funsym fsym
             | T_sequence.(SeqEpsilon | SeqSymbol _), [] -> str_of_funsym fsym
             | ( T_sequence.(
                   SeqConcat _ | SeqLeftQuotient _ | SeqRightQuotient _),
                 [ t1; t2 ] ) ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
                      (t2 (Priority.fun_app + 1))
             | T_regex.(RegEmpty | RegFull | RegEpsilon), [] ->
                 str_of_funsym fsym
             | ( T_regex.(RegStr | RegComplement | RegStar | RegPlus | RegOpt),
                 [ t1 ] ) ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
             | T_regex.(RegConcat | RegUnion | RegInter), [ t1; t2 ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
                      (t2 (Priority.fun_app + 1))
             | T_array.AConst _, [ t1 ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
             | T_array.AStore _, [ t1; t2; t3 ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s %s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
                      (t2 (Priority.fun_app + 1))
                      (t3 (Priority.fun_app + 1))
             | T_array.ASelect _, [ t1; t2 ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s[%s]" (t1 Priority.highest) (t2 Priority.lowest)
             | T_tuple.TupleCons sorts, args ->
                 Priority.add_paren priority Priority.comma
                 @@ String.concat_map_list ~sep:"," (List.zip_exn args sorts)
                      ~f:(fun (t, s) ->
                        t (Priority.comma + 1) (*ToDo*) ^ ":" ^ str_of_sort s)
             | T_tuple.TupleSel (_, _), [ t ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s" (str_of_funsym fsym)
                      (t (Priority.fun_app + 1))
             | T_dt.DTCons ("::", _, dt), [ _; _ ]
               when Datatype.is_list_sort (Datatype.sort_of dt) -> (
                 let rec aux args = function
                   | FunApp (T_dt.DTCons ("::", _, dt), [ t1; t2 ], _)
                     when Datatype.is_list_sort (Datatype.sort_of dt) ->
                       aux (args @ [ t1 ]) t2
                   | FunApp (T_dt.DTCons ("[]", _, dt), [], _)
                     when Datatype.is_list_sort (Datatype.sort_of dt) ->
                       (args, None)
                   | t -> (args, Some t)
                 in
                 let t1, t2 =
                   match ts with [ t1; t2 ] -> (t1, t2) | _ -> assert false
                 in
                 match aux [ t1 ] t2 with
                 | args, None ->
                     Priority.add_paren priority Priority.lowest
                     (*ToDo*) @@ String.bracket
                     @@ String.concat_map_list ~sep:"; " args
                          ~f:(str_of ~priority:(Priority.seq + 1) (*ToDo*))
                 | [ t1 ], Some t2 ->
                     Priority.add_paren priority Priority.cons
                     @@ sprintf "%s :: %s"
                          (str_of ~priority:(Priority.cons + 1) t1)
                          (str_of ~priority:Priority.cons t2)
                 | args, Some t ->
                     Priority.add_paren priority Priority.append_power
                     @@ sprintf "%s @ %s"
                          (String.bracket
                          @@ String.concat_map_list ~sep:"; " args
                               ~f:(str_of ~priority:(Priority.seq + 1) (*ToDo*))
                          )
                          (str_of ~priority:Priority.append_power t))
             | T_dt.DTCons (_, _, _), [] -> str_of_funsym fsym
             | T_dt.DTCons (_, _, _), ts ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s" (str_of_funsym fsym)
                      (String.concat_map_list ~sep:" " ts ~f:(fun t ->
                           t (Priority.fun_app + 1)))
             | T_dt.DTSel (_, _, _), [ t1 ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "%s %s" (str_of_funsym fsym)
                      (t1 (Priority.fun_app + 1))
             | T_ref.Ref _sort, [ t ] ->
                 Priority.add_paren priority Priority.fun_app
                 @@ sprintf "ref %s" (t (Priority.fun_app + 1))
             | T_ref.Deref _sort, [ t ] ->
                 Priority.add_paren priority Priority.neg_deref
                 @@ sprintf "!%s" (t (Priority.neg_deref + 1))
             | T_ref.Update _sort, [ t1; t2 ] ->
                 Priority.add_paren priority Priority.assign
                 @@ sprintf "%s := %s"
                      (t1 (Priority.assign + 1))
                      (t2 Priority.assign)
             | f, ts ->
                 failwith
                   ("unknown function application: " ^ String.concat ~sep:" "
                   @@ str_of_funsym f
                      :: List.map ts ~f:(fun t -> t (Priority.fun_app + 1)))

           method flet tvar _sort (_, def) (_, body) priority =
             Priority.add_paren priority Priority.let_forall_exists
             @@ sprintf "let %s = %s in %s" (Ident.name_of_tvar tvar)
                  (def Priority.let_forall_exists (*ToDo*))
                  (body Priority.let_forall_exists (*ToDo*))
           (*sprintf "let %s:%s = %s in %s" (Ident.name_of_tvar tvar) (short_name_of_sort sort) (def Priority.lowest(*ToDo*)) (body Priority.lowest(*ToDo*))*)
        end)
      t0 priority

  (** Observation *)

  let is_var = function
    | Var (_, _, _) -> true
    | FunApp
        ( T_bool.Formula
            (Formula.Atom (Atom.App (Predicate.Var (Ident.Pvar _, []), [], _), _)),
          _,
          _ ) ->
        true
    | _ -> false

  let is_app = function FunApp (_, _, _) -> true | _ -> false

  let is_fvar_app = function
    | FunApp (FVar (_, _, _), _, _) -> true
    | _ -> false

  let is_funcall = function FunApp (FunCall _, _, _) -> true | _ -> false
  let is_let_term = function LetTerm _ -> true | _ -> false

  let rec is_compound = function
    | Var _ -> false
    | FunApp
        ( ( FVar (_, _, _)
          | T_int.Int _
          | T_real.(Real _ | Alge _)
          | T_bv.BVNum _ | T_string.StrConst _ ),
          [],
          _ ) ->
        false
    | FunApp (_, _, _) -> true
    | LetTerm (_, _, _, body, _) -> is_compound body

  let rec is_pathexp = function
    | Var (_, _, _) -> true
    | FunApp (FVar (_, _, _), ts, _) -> List.exists ts ~f:is_pathexp
    | FunApp
        ( ( T_int.(Neg | Nop | Abs)
          | T_real.(RNeg | RAbs)
          | T_bv.(BVNot _ | BVNeg _ | BVEXTRACT _ | BVSEXT _ | BVZEXT _)
          | T_irb.(IntToReal | RealToInt | IntToBV _ | BVToInt _)
          | T_num.(NNeg _ | NSEXT _) ),
          [ t ],
          _ ) ->
        is_pathexp t
    | FunApp
        ( T_dt.DTSel (sel_name, dt, _),
          [ FunApp (T_dt.DTCons (cons_name, _, _), _, _) ],
          _ ) -> (
        match Datatype.look_up_cons dt cons_name with
        | Some cons ->
            not
            @@ List.exists
                 (Datatype.sels_of_cons cons)
                 ~f:(Datatype.name_of_sel >> String.( = ) sel_name)
        | None -> assert false)
    | FunApp (T_dt.DTSel (_, _, _), [ t1 ], _) -> is_pathexp t1
    | FunApp (T_array.ASelect _, [ t1; _ ], _) -> is_pathexp t1
    | _ -> false

  (* assume [t] is simplified*)
  let is_uninterpreted_term = function
    (* | Var (_, _, _) -> true *)
    | FunApp (T_int.(Div _ | Rem _), [ _; t2 ], _) -> T_int.is_zero t2
    | FunApp (T_dt.DTSel _, [ t1 ], _) -> T_dt.is_cons t1 (*ToDo*)
    | FunApp (T_array.ASelect _, _, _) -> true (*ToDo*)
    | _ -> false

  let is_let_free =
    fold
      ~f:
        (object
           method fvar _tvar _sort = true

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] -> Formula.is_let_free phi
             | _ -> List.for_all args ~f:Fn.id

           method flet _tvar _sort _def _body = false
        end)

  let is_quantifier_free =
    fold
      ~f:
        (object
           method fvar _tvar _sort = true

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] -> Formula.is_quantifier_free phi
             | _ -> List.for_all args ~f:Fn.id

           method flet _tvar _sort def body = def && body
        end)

  let tvs_of =
    fold
      ~f:
        (object
           method fvar tvar _ = Set.Poly.singleton tvar

           method fapp fsym args =
             Set.Poly.union_list
             @@
             match fsym with
             | FVar (tvar, _, _)
               when not @@ Hash_set.Poly.mem defined_fvars tvar ->
                 Set.Poly.singleton tvar :: args
             | T_bool.Formula phi -> Formula.tvs_of phi :: args
             | _ -> args

           method flet tvar _sort def body =
             Set.union def (Set.remove body tvar)
        end)

  let pvs_of =
    fold
      ~f:
        (object
           method fvar _ _ = Set.Poly.empty

           method fapp fsym args =
             Set.Poly.union_list
             @@
             match fsym with
             | T_bool.Formula phi -> Formula.pvs_of phi :: args
             | _ -> args

           method flet x _sort def body =
             Set.union def (Set.remove body (Ident.tvar_to_pvar x))
        end)

  let fvs_of atm =
    Set.union (tvs_of atm)
    @@ Set.Poly.map ~f:Ident.pvar_to_tvar
    (*ToDo*) @@ pvs_of atm

  let svs_of =
    let let_svar = function
      | Sort.SVar svar -> Set.Poly.singleton svar
      | _ -> Set.Poly.empty
    in
    fold
      ~f:
        (object
           method fvar _ sort = let_svar sort

           method fapp fsym args =
             Set.Poly.union_list
             @@
             match fsym with
             | T_bool.Formula phi -> Formula.svs_of phi :: args
             | _ -> (* ToDo: fsym may contain sort variables? *) args

           method flet _ sort def body =
             Set.Poly.union_list [ def; body; let_svar sort ]
        end)

  let term_sort_env_of ?(bvs = Set.Poly.empty) t =
    fold
      ~f:
        (object
           method fvar x sort bvs =
             if Set.mem bvs x then Set.Poly.empty
             else Set.Poly.singleton (x, sort)

           method fapp fsym args bvs =
             Set.Poly.union_list
             @@ (match fsym with
                | FVar (x, sargs, sret)
                  when not @@ Hash_set.Poly.mem defined_fvars x ->
                    Set.Poly.singleton (x, Sort.mk_fun (sargs @ [ sret ]))
                | T_bool.Formula phi -> Formula.term_sort_env_of ~bvs phi
                | _ -> Set.Poly.empty)
                :: List.map args ~f:(fun t -> t bvs)

           method flet x sort def body bvs =
             Set.(remove (union (def bvs) (body (add bvs x))) (x, sort))
        end)
      t bvs

  let pred_sort_env_of ?(bpvs = Set.Poly.empty) t =
    fold
      ~f:
        (object
           method fvar _ _ _ = Set.Poly.empty

           method fapp fsym args bpvs =
             Set.Poly.union_list
             @@ (match fsym with
                | T_bool.Formula phi -> Formula.pred_sort_env_of ~bpvs phi
                | _ -> Set.Poly.empty)
                :: List.map args ~f:(fun t -> t bpvs)

           method flet _ _ def body bpvs = Set.union (def bpvs) (body bpvs)
        end)
      t bpvs

  let sort_env_of ?(bpvs = Set.Poly.empty) t =
    Set.union (term_sort_env_of t)
    @@ pred_to_sort_env @@ pred_sort_env_of ~bpvs t

  let rec value_of = function
    | FunApp (T_bool.Formula (Formula.Atom (Atom.True _, _)), _, _) ->
        Value.Bool true
    | FunApp (T_bool.Formula (Formula.Atom (Atom.False _, _)), _, _) ->
        Value.Bool false
    | FunApp (T_int.Int n, _, _) -> Value.Int n
    | FunApp (T_real.Real r, _, _) -> Value.Real r
    | FunApp (T_bv.BVNum (size, i), [], _) -> Value.BV (size, i)
    | FunApp (T_array.AConst (si, _), [ t ], _) ->
        Value.Arr (value_of @@ mk_dummy si, value_of t, Map.Poly.empty)
    | FunApp (T_array.AStore _, [ t1; t2; t3 ], _) -> (
        match value_of t1 with
        | Value.Arr (dummy, v, m) ->
            let v2 = value_of t2 in
            let v3 = value_of t3 in
            if Value.equal v v3 then Value.Arr (dummy, v, m)
            else Value.Arr (dummy, v, Map.Poly.set m ~key:v2 ~data:v3)
        | _ ->
            failwith @@ "Array store: first term must be an array, but got "
            ^ Term.str_of t1)
    | FunApp (T_tuple.TupleCons sorts, ts, _) ->
        let ts' = List.map ~f:value_of ts in
        if List.length ts' <> List.length sorts then
          failwith "Tuple constructor: number of terms does not match sorts";
        Value.TupleCons ts'
    | FunApp (T_dt.DTCons (name, sorts, dt), ts, _) ->
        let vs = List.map ~f:value_of ts in
        if List.length vs <> List.length sorts then
          failwith "Datatype constructor: number of terms does not match sorts";
        Value.DTCons
          ( name,
            List.map (Datatype.params_of dt) ~f:(Term.mk_dummy >> value_of),
            vs )
    | t -> failwith @@ "[value_of] " ^ str_of t

  let funsyms_of =
    fold
      ~f:
        (object
           method fvar _ _ = Set.Poly.empty

           method fapp fsym args =
             Set.union (Set.Poly.union_list args)
             @@
             match fsym with
             | T_bool.Formula phi -> Formula.funsyms_of phi
             | _ -> Set.Poly.singleton fsym

           method flet _ _ def body = Set.union def body
        end)

  let predsyms_of =
    fold
      ~f:
        (object
           method fvar _ _ = Set.Poly.empty

           method fapp fsym args =
             Set.union (Set.Poly.union_list args)
             @@
             match fsym with
             | T_bool.Formula phi -> Formula.predsyms_of phi
             | _ -> Set.Poly.empty

           method flet _ _ def body = Set.union def body
        end)

  let rec fvar_apps_of = function
    | Var _ -> Set.Poly.empty
    | FunApp (fsym, args, _) as t ->
        Set.Poly.union_list
        @@ (match fsym with
           | FVar (_, _, _) -> Set.Poly.singleton t
           | T_bool.Formula phi -> Formula.fvar_apps_of phi
           | _ -> Set.Poly.empty)
           :: List.map args ~f:fvar_apps_of
    | LetTerm (_, _, def, body, _) ->
        Set.union (fvar_apps_of def) (fvar_apps_of body)

  let rec number_of_quantifiers = function
    | Var _ -> 0
    | FunApp (fsym, args, _) ->
        Integer.sum_list
        @@ (match fsym with
           | T_bool.Formula phi -> Formula.number_of_quantifiers phi
           | _ -> 0)
           :: List.map args ~f:number_of_quantifiers
    | LetTerm (_, _, def, body, _) ->
        number_of_quantifiers def + number_of_quantifiers body

  let rec pathexps_of ?(bvs = Set.Poly.empty) t =
    if is_pathexp t then Set.Poly.singleton t
    else
      match t with
      | Var (var, _, _) ->
          if Set.mem bvs var then Set.Poly.empty else Set.Poly.singleton t
      | FunApp (fsym, args, _) ->
          Set.Poly.union_list
          @@ (match fsym with
             | FVar (_, _, _) -> Set.Poly.singleton t
             | T_bool.Formula phi -> Formula.pathexps_of ~bvs phi
             | _ -> Set.Poly.empty)
             :: List.map args ~f:(pathexps_of ~bvs)
      | LetTerm (x, _, def, body, _) ->
          Set.(union (pathexps_of ~bvs def) (pathexps_of ~bvs:(add bvs x) body))

  let rec filtered_terms_of ~f t =
    Set.union
      (if f t then Set.Poly.singleton t else Set.Poly.empty)
      (match t with
      | FunApp (T_bool.Formula phi, _, _) -> Formula.filtered_terms_of ~f phi
      | FunApp (_, args, _) ->
          Set.Poly.union_list @@ List.map args ~f:(filtered_terms_of ~f)
      | LetTerm (_, _, def, body, _) ->
          Set.union (filtered_terms_of ~f def) (filtered_terms_of ~f body)
      | _ -> Set.Poly.empty)

  let rec atoms_of ?(pos = true) = function
    | Var (_, _, _) -> (Set.Poly.empty, Set.Poly.empty)
    | FunApp (T_bool.Formula phi, args, _) ->
        assert (List.is_empty args);
        let pos, neg = Formula.atoms_of ~pos phi in
        let poss1, negs1 = List.unzip @@ List.map args ~f:Term.atoms_of in
        (Set.Poly.union_list (pos :: poss1), Set.Poly.union_list (neg :: negs1))
    | FunApp (_fsym, args, _) ->
        let poss1, negs1 = List.unzip @@ List.map args ~f:Term.atoms_of in
        (* ToDo: distinction between pos and neg is arbitrary since fsym is ignored *)
        (Set.Poly.union_list poss1, Set.Poly.union_list negs1)
    | LetTerm (_, _, def, body, _) ->
        let pos1, neg1 = atoms_of ~pos def in
        let pos2, neg2 = atoms_of ~pos body in
        (Set.union pos1 pos2, Set.union neg1 neg2)

  (* assume that the argument is let-normalized *)
  let rec body_of_let = function
    | LetTerm (_, _, _, body, _) -> body_of_let body
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp (T_bool.Formula (Formula.body_of_let phi), [], info)
    | t -> t

  let rec number_of_pvar_apps ?(ex = Map.Poly.empty) is_pos = function
    | FunApp (T_bool.Formula phi, _, _) ->
        Formula.number_of_pvar_apps ~ex is_pos phi
    | LetTerm (x, _, def, body, _) ->
        let def_size = number_of_pvar_apps ~ex is_pos def in
        number_of_pvar_apps
          ~ex:(Map.Poly.set ~key:x ~data:def_size ex)
          is_pos body
    | Var (x, _, _) -> (
        match Map.Poly.find ex x with Some i -> i | None -> 0)
    | FunApp (_, ts, _) ->
        Integer.sum_list @@ List.map ts ~f:(number_of_pvar_apps ~ex is_pos)

  let ast_size t =
    let rec ast_size ~ex = function
      | Var (var, _, _) -> (
          match Map.Poly.find ex var with
          | Some size -> size (*ToDo*)
          | None -> 1)
      | FunApp (sym, args, _) -> (
          Integer.sum_list (1 :: List.map ~f:(ast_size ~ex) args)
          +
          match sym with
          | T_bool.Formula phi -> Formula.ast_size (*ToDo*) phi - 1
          | _ -> 0)
      | LetTerm (var, _, def, body, _) ->
          ast_size ~ex:(Map.Poly.set ex ~key:var ~data:(ast_size ~ex def)) body
    in
    ast_size ~ex:Map.Poly.empty t

  let rec occur_times ?(map = Map.Poly.empty) x = function
    | Var (tvar, _, _) -> (
        if Stdlib.(x = tvar) then 1
        else match Map.Poly.find map tvar with Some i -> i | _ -> 0)
    | FunApp (T_bool.Formula phi, _, _) -> Formula.occur_times ~map x phi
    | FunApp (_, ts, _) ->
        Integer.sum_list @@ List.map ts ~f:(occur_times ~map x)
    | LetTerm (var, _, def, body, _) ->
        let map =
          Map.Poly.add_exn ~key:var ~data:(occur_times ~map x def) map
        in
        occur_times ~map x body

  let rec sort_of = function
    | Var (_, sort, _) -> sort
    | FunApp (FVar (_, sargs, sret), args, _) ->
        Sort.mk_fun @@ (List.drop sargs @@ List.length args) @ [ sret ]
    | FunApp (T_bool.Formula _, [], _) -> T_bool.SBool
    | FunApp (T_bool.IfThenElse, [ _; t; _ ], _) -> sort_of t
    | FunApp (T_int.Int _, [], _)
    | FunApp
        ((T_int.(Neg | Nop | Abs) | T_irb.(RealToInt | BVToInt _)), [ _ ], _)
    | FunApp (T_int.(Add | Sub | Mul | Div _ | Rem _), _, _) ->
        T_int.SInt
    | FunApp (T_real.(Real _ | Alge _), [], _)
    | FunApp ((T_real.(RNeg | RAbs) | T_irb.IntToReal), [ _ ], _)
    | FunApp (T_real.(RAdd | RSub | RPower | RMul | RDiv), _, _) ->
        T_real.SReal
    | FunApp (T_bv.BVNum (size, _), [], _)
    | FunApp ((T_bv.BVNot size | T_bv.BVNeg size | T_irb.IntToBV size), [ _ ], _)
    | FunApp
        ( T_bv.(
            ( BVNot size
            | BVAnd size
            | BVOr size
            | BVXor size
            | BVNand size
            | BVNor size
            | BVXnor size
            | BVAdd size
            | BVSub size
            | BVMul size
            | BVDiv (size, _)
            | BVRem (size, _)
            | BVSMod size
            | BVSHL size
            | BVLSHR size
            | BVASHR size )),
          _,
          _ ) ->
        T_bv.SBV size
    | FunApp (T_bv.BVEXTRACT (_size, h, l), [ _ ], _) ->
        T_bv.SBV (Some (h - l + 1))
    | FunApp (T_bv.(BVSEXT (size, ext) | BVZEXT (size, ext)), [ _ ], _) ->
        T_bv.SBV (T_bv.ext_size size ext)
    | FunApp (T_bv.BVCONCAT (size1, size2), _, _) ->
        T_bv.SBV (T_bv.add_size size1 size2)
    | FunApp (T_num.Value (_, sv), [], _)
    | FunApp (T_num.(NNeg sv | NSEXT (_, _, _, sv)), [ _ ], _)
    | FunApp
        ( T_num.(
            ( NAdd sv
            | NSub sv
            | NMul sv
            | NDiv (sv, _)
            | NRem (sv, _)
            | NPower sv )),
          _,
          _ ) ->
        Sort.SVar sv
    | FunApp (T_string.StrConst _, _, _) -> T_string.SString
    | FunApp (T_sequence.(SeqEpsilon | SeqSymbol _), [], _) ->
        T_sequence.SSequence true
    | FunApp
        ( T_sequence.(SeqConcat fin | SeqLeftQuotient fin | SeqRightQuotient fin),
          [ _; _ ],
          _ ) ->
        T_sequence.SSequence fin
    | FunApp (T_regex.(RegEmpty | RegFull | RegEpsilon), [], _) ->
        T_regex.SRegEx
    | FunApp
        (T_regex.(RegStr | RegComplement | RegStar | RegPlus | RegOpt), [ _ ], _)
      ->
        T_regex.SRegEx
    | FunApp (T_regex.(RegConcat | RegUnion | RegInter), [ _; _ ], _) ->
        T_regex.SRegEx
    | FunApp (T_array.AConst (s1, s2), _, _) -> T_array.SArray (s1, s2)
    | FunApp (T_array.AStore (s1, s2), [ _; _; _ ], _) -> T_array.SArray (s1, s2)
    | FunApp (T_array.ASelect (_s1, s2), [ _; _ ], _) -> s2
    | FunApp (T_tuple.TupleCons sorts, _, _) -> T_tuple.STuple sorts
    | FunApp (T_tuple.TupleSel (sorts, i), [ _ ], _) -> List.nth_exn sorts i
    | FunApp (T_dt.DTCons (_, _, dt), _, _) -> Datatype.sort_of dt
    | FunApp (T_dt.DTSel (_, _, sort), _, _) -> sort
    | FunApp (T_ref.Ref sort, [ _ ], _) -> T_ref.SRef sort
    | FunApp (T_ref.Deref sort, [ _ ], _) -> sort
    | FunApp (T_ref.Update _, [ _; _ ], _) -> Datatype.mk_unit_sort ()
    | LetTerm (_, _, _, body, _) -> sort_of body
    | t -> failwith ("error at sort_of: " ^ str_of t)

  and div_rem_of = function
    | Var (_, _, _) -> Set.Poly.empty
    | FunApp (T_bool.Formula phi, [], _) -> Formula.div_rem_of phi
    | FunApp (T_int.(Div _ | Rem _), [ t1; t2 ], _) ->
        Set.add (Set.union (div_rem_of t1) (div_rem_of t2)) (t1, t2)
    | FunApp (_, args, _) -> Set.Poly.union_list @@ List.map ~f:div_rem_of args
    | LetTerm (_, _, def, body, _) ->
        Set.union (div_rem_of def) (div_rem_of body)

  (** Substitution *)

  let rec rename map = function
    | Var (var', sort, info) as t -> (
        match Map.Poly.find map var' with
        | None -> t
        | Some var -> Var (var, sort, info))
    | FunApp (sym, ts, info) ->
        FunApp (rename_fun_sym map sym, List.map ~f:(rename map) ts, info)
    | LetTerm (var, sort, def, body, info) -> (
        match Map.Poly.find map var with
        | Some var -> LetTerm (var, sort, rename map def, rename map body, info)
        | None -> LetTerm (var, sort, rename map def, rename map body, info))

  let rec rename_pvars map = function
    | FunApp (sym, args, info) ->
        FunApp
          ( rename_pvars_fun_sym map sym,
            List.map ~f:(rename_pvars map) args,
            info )
    | LetTerm (var, sort, def, body, info) ->
        LetTerm (var, sort, rename_pvars map def, rename_pvars map body, info)
    | t -> t

  let rec rename_sorted_pvars map = function
    | FunApp (sym, args, info) ->
        FunApp
          ( rename_sorted_pvars_fun_sym map sym,
            List.map ~f:(rename_sorted_pvars map) args,
            info )
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          ( var,
            sort,
            rename_sorted_pvars map def,
            rename_sorted_pvars map body,
            info )
    | t -> t

  let rec alpha_rename_let ?(map = Map.Poly.empty) = function
    | Var (var, sort, info) ->
        Var
          ( (match Map.Poly.find map var with Some v -> v | None -> var),
            sort,
            info )
    | FunApp (fsym, ts, info) ->
        FunApp
          ( alpha_rename_let_fun_sym ~map fsym,
            List.map ts ~f:(alpha_rename_let ~map),
            info )
    | LetTerm (var, sort, def, body, info) ->
        let var' = Ident.mk_fresh_tvar () in
        let map' = Map.Poly.set ~key:var ~data:var' map in
        LetTerm
          ( var',
            sort,
            alpha_rename_let ~map def,
            alpha_rename_let ~map:map' body,
            info )

  (* assume that [phi] is let-normalized *)
  let rec replace_let_formula_body phi new_body =
    match phi with
    | Formula.LetFormula (var, sort, def, body, info) ->
        LetTerm (var, sort, def, replace_let_formula_body body new_body, info)
    | _ -> new_body (*ToDo*)

  (* assume that [term] is let-normalized *)
  let rec replace_let_body term new_body =
    match term with
    | LetTerm (var, sort, def, body, info) ->
        LetTerm (var, sort, def, replace_let_body body new_body, info)
    | FunApp (T_bool.Formula phi, [], _) when Formula.is_let_formula phi ->
        replace_let_formula_body phi new_body
    | _ -> new_body (*ToDo*)

  let rec subst map = function
    | Var (var', sort, info) -> (
        match Map.Poly.find map var' with
        | None -> Var (var', sort, info)
        | Some t -> t)
    | FunApp (sym, ts, info) ->
        FunApp (subst_fun_sym str_of map sym, List.map ~f:(subst map) ts, info)
    | LetTerm (var, sort, def, body, info) ->
        assert (not @@ Map.Poly.mem map var);
        LetTerm (var, sort, subst map def, subst map body, info)

  let subst_preds psub t =
    fold
      ~f:
        (object
           method fvar tvar sort psub =
             match Map.Poly.find psub (Ident.tvar_to_pvar (*ToDo*) tvar) with
             | Some (senv, phi) ->
                 if List.is_empty senv then
                   T_bool.of_formula (Formula.subst_preds (*ToDO*) psub phi)
                 else assert false
             | None -> Term.mk_var tvar sort

           method fapp fsym args psub =
             let args = List.map args ~f:(fun t -> t psub) in
             match fsym with
             | T_bool.Formula phi ->
                 mk_fsym_app
                   (T_bool.Formula (Formula.subst_preds psub phi))
                   args
             | _ -> mk_fsym_app fsym args

           method flet tvar sort def body psub =
             let psub' =
               Map.Poly.remove psub (Ident.tvar_to_pvar (*ToDo*) tvar)
             in
             Term.mk_let_term tvar sort (def psub) (body psub')
        end)
      t psub

  let subst_funcs fsub t =
    fold
      ~f:
        (object
           method fvar tvar sort fsub =
             match Map.Poly.find fsub tvar with
             | Some (senv, t) -> if List.is_empty senv then t else assert false
             | None -> Term.mk_var tvar sort

           method fapp fsym args fsub =
             let args = List.map args ~f:(fun t -> t fsub) in
             match fsym with
             | T_bool.Formula phi ->
                 mk_fsym_app
                   (T_bool.Formula (Formula.subst_funcs fsub phi))
                   args
             | FVar (tvar, _, _) -> (
                 match Map.Poly.find fsub tvar with
                 | Some (senv, t) ->
                     let tsub =
                       TermSubst.make ~name:(Ident.name_of_tvar tvar) senv args
                     in
                     Term.subst tsub t
                 | None -> mk_fsym_app fsym args)
             | _ -> mk_fsym_app fsym args

           method flet tvar sort def body fsub =
             let fsub' = Map.Poly.remove fsub tvar in
             Term.mk_let_term tvar sort (def fsub) (body fsub')
        end)
      t fsub

  let rec subst_sorts map = function
    | Var (x, sort, info) -> Var (x, subst_sorts_sort map sort, info)
    (*| FunApp (T_irb.IntToReal, [Var (tvar, _, info)], _) ->
      Var (tvar, T_real.SReal, info)
      | FunApp (T_irb.RealToInt, [Var (tvar, _, info)], _) ->
      Var (tvar, T_int.SInt, info)
      | FunApp (T_string.StrConst str, _, info) ->
      Var (Ident.Tvar ("\"" ^ str ^ "\""), T_string.SString, info)*)
    | FunApp (sym, args, info) ->
        FunApp
          (subst_sorts_fun_sym map sym, List.map ~f:(subst_sorts map) args, info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          ( var,
            subst_sorts_sort map sort,
            subst_sorts map def,
            subst_sorts map body,
            info )

  let rec subst_conts map = function
    | Var (x, sort, info) -> Var (x, subst_conts_sort map sort, info)
    (*| FunApp (T_irb.IntToReal, [Var (tvar, _, info)], _) ->
      Var (tvar, T_real.SReal, info)
      | FunApp (T_irb.RealToInt, [Var (tvar, _, info)], _) ->
      Var (tvar, T_int.SInt, info)
      | FunApp (T_string.StrConst str, _, info) ->
      Var (Ident.Tvar ("\"" ^ str ^ "\""), T_string.SString, info)*)
    | FunApp (sym, args, info) ->
        FunApp
          (subst_conts_fun_sym map sym, List.map ~f:(subst_conts map) args, info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          ( var,
            subst_conts_sort map sort,
            subst_conts map def,
            subst_conts map body,
            info )

  let rec subst_opsigs map = function
    | Var (x, sort, info) -> Var (x, subst_opsigs_sort map sort, info)
    (*| FunApp (T_irb.IntToReal, [Var (tvar, _, info)], _) ->
      Var (tvar, T_real.SReal, info)
      | FunApp (T_irb.RealToInt, [Var (tvar, _, info)], _) ->
      Var (tvar, T_int.SInt, info)
      | FunApp (T_string.StrConst str, _, info) ->
      Var (Ident.Tvar ("\"" ^ str ^ "\""), T_string.SString, info)*)
    | FunApp (sym, args, info) ->
        FunApp
          ( subst_opsigs_fun_sym map sym,
            List.map ~f:(subst_opsigs map) args,
            info )
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          ( var,
            subst_opsigs_sort map sort,
            subst_opsigs map def,
            subst_opsigs map body,
            info )

  let aconv_tvar =
    fold
      ~f:
        (object
           method fvar tvar sort = mk_var tvar sort

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] ->
                 mk_fsym_app (T_bool.Formula (Formula.aconv_tvar phi)) []
             | _, _ -> mk_fsym_app fsym args

           method flet tvar sort def body = mk_let_term tvar sort def body
        end)

  let aconv_tvar_norm next =
    fold
      ~f:
        (object
           method fvar tvar sort = mk_var tvar sort

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] ->
                 mk_fsym_app
                   (T_bool.Formula (Formula.aconv_tvar_norm next phi))
                   []
             | _, _ -> mk_fsym_app fsym args

           method flet tvar sort def body = mk_let_term tvar sort def body
        end)

  let aconv_pvar =
    fold
      ~f:
        (object
           method fvar tvar sort = mk_var tvar sort

           method fapp fsym args =
             match (fsym, args) with
             | T_bool.Formula phi, [] ->
                 mk_fsym_app (T_bool.Formula (Formula.aconv_pvar phi)) []
             | _, _ -> mk_fsym_app fsym args

           method flet tvar sort def body = mk_let_term tvar sort def body
        end)

  (* assume that the argument is alpha-renamed *)

  (** Observation *)

  let rec let_env_of ?(map = Map.Poly.empty) = function
    | Var _ -> map
    | FunApp (T_bool.Formula phi, [], _) -> Formula.let_env_of ~map phi
    | FunApp (_, ts, _) ->
        List.fold ts ~init:map ~f:(fun map -> let_env_of ~map)
    | LetTerm (var, _, def, body, _) ->
        let_env_of ~map:(Map.Poly.set map ~key:var ~data:(subst map def)) body

  (* assume that the argument is alpha-renamed *)
  let rec let_sort_env_of ?(map = Map.Poly.empty) = function
    | Var _ -> map
    | FunApp (T_bool.Formula phi, [], _) -> Formula.let_sort_env_of ~map phi
    | FunApp (_, ts, _) ->
        List.fold ts ~init:map ~f:(fun map -> let_sort_env_of ~map)
    | LetTerm (var, sort, _, body, _) ->
        let_sort_env_of ~map:(Map.Poly.set map ~key:var ~data:sort) body

  (** Construction *)

  let insert_let_term tvar sort def info term =
    if Set.mem (tvs_of term) tvar then
      let tvar' = Ident.mk_fresh_tvar () in
      LetTerm
        (tvar', sort, def, rename (Map.Poly.singleton tvar tvar') term, info)
    else term

  (** Transformation *)

  let rec elim_neq = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp (T_bool.Formula (Formula.elim_neq phi), [], info)
    | FunApp (fsym, ts, info) -> FunApp (fsym, List.map ts ~f:elim_neq, info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm (var, sort, elim_neq def, elim_neq body, info)

  (* ToDo: it elim_ite requires that LetTerm is eliminated *)
  let rec elim_ite = function
    | Var (var, sort, info) -> [ (Formula.mk_true (), Var (var, sort, info)) ]
    | FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], _) ->
        let cond = Formula.elim_ite @@ Formula.of_bool_term t1 in
        let ncond = Formula.mk_neg cond in
        List.map (elim_ite t2) ~f:(fun (phi, t) -> (Formula.mk_and cond phi, t))
        @ List.map (elim_ite t3) ~f:(fun (phi, t) ->
              (Formula.mk_and ncond phi, t))
    | FunApp (T_bool.Formula phi, [], info) ->
        [
          ( Formula.mk_true (),
            FunApp (T_bool.Formula (Formula.elim_ite phi), [], info) );
        ]
    (* | FunApp (T_int.Neg, [t1], _) ->
       List.map (elim_ite t1) ~f:(fun (phi, t) -> phi, T_int.mk_neg t) *)
    | FunApp (fsym (* ToDo *), [ t1 ], _) ->
        List.map (elim_ite t1) ~f:(fun (phi, t) ->
            (phi, Term.mk_fsym_app fsym [ t ]))
    (* | FunApp
        ( (( T_int.(Add | Sub | Mul | Div _ | Rem _)
           | T_real.(RAdd | RSub | RMul | RDiv) ) as fsym),
          [ t1; t2 ],
          _ ) -> *)
    | FunApp (fsym (* ToDo *), [ t1; t2 ], _) ->
        List.cartesian_product (elim_ite t1) (elim_ite t2)
        |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
               (Formula.and_of [ phi1; phi2 ], Term.mk_fsym_app fsym [ t1; t2 ]))
    | term ->
        if false then print_endline ("can't elim ite :" ^ Term.str_of term);
        [ (Formula.mk_true (), term) ]

  let rec elim_pvars unknowns = function
    | Var (_, _, _) as term -> term
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp (T_bool.Formula (Formula.elim_pvars unknowns phi), [], info)
    | FunApp (fsym, ts, info) ->
        FunApp (fsym, List.map ts ~f:(elim_pvars unknowns), info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          (var, sort, elim_pvars unknowns def, elim_pvars unknowns body, info)

  (** eliminate let-binding that contains an unknown to be synthesized if the
      argument is let-normalized, then the return value is let-normalized *)
  let rec elim_let_with_unknowns ?(map = Map.Poly.empty) unknowns = function
    | Var (var, _, _) as term -> (
        match Map.Poly.find map var with Some t -> t | None -> term)
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp
          ( T_bool.Formula (Formula.elim_let_with_unknowns ~map unknowns phi),
            [],
            info )
    | FunApp (fsym, ts, info) ->
        FunApp
          (fsym, List.map ts ~f:(elim_let_with_unknowns ~map unknowns), info)
    | LetTerm (var, sort, def, body, info) ->
        let def' = elim_let_with_unknowns ~map unknowns def in
        if Set.disjoint (Term.fvs_of def') unknowns then
          LetTerm
            (var, sort, def', elim_let_with_unknowns ~map unknowns body, info)
        else
          elim_let_with_unknowns
            ~map:(Map.Poly.set map ~key:var ~data:def')
            unknowns body

  let rec elim_let ?(map = Map.Poly.empty) = function
    | Var (var, _, _) as term -> (
        match Map.Poly.find map var with Some t -> t | None -> term)
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp (T_bool.Formula (Formula.elim_let ~map phi), [], info)
    | FunApp (fsym, ts, info) ->
        FunApp (fsym, List.map ts ~f:(elim_let ~map), info)
    | LetTerm (var, _, def, body, _) ->
        elim_let ~map:(Map.Poly.set map ~key:var ~data:(elim_let ~map def)) body

  let rec instantiate_div0_mod0 = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (T_int.(Div _ | Rem _), [ t1; t2 ], _) when T_int.is_zero t2 ->
        mk_var (Ident.mk_dontcare (Term.str_of t1)) T_int.SInt
    | FunApp (sym, args, info) ->
        let sym =
          match sym with
          | T_bool.Formula phi ->
              T_bool.Formula (Formula.instantiate_div0_mod0 phi)
          | sym -> sym
        in
        FunApp (sym, List.map ~f:instantiate_div0_mod0 args, info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          ( var,
            sort,
            instantiate_div0_mod0 def,
            instantiate_div0_mod0 body,
            info )

  let rec extend_pred_params pvar extended_params = function
    | Var (tvar, sort, info) -> Var (tvar, sort, info)
    | FunApp (sym, args, info) ->
        let sym =
          match sym with
          | T_bool.Formula phi ->
              T_bool.Formula
                (Formula.extend_pred_params pvar extended_params phi)
          | sym -> sym
        in
        FunApp
          (sym, List.map ~f:(extend_pred_params pvar extended_params) args, info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          ( var,
            sort,
            extend_pred_params pvar extended_params def,
            extend_pred_params pvar extended_params body,
            info )

  let rec replace_div_mod map = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (T_int.Div _, [ t1; t2 ], _) ->
        let divvar, _ = Map.Poly.find_exn map (t1, t2) in
        Var (divvar, T_int.SInt, Dummy)
    | FunApp (T_int.Rem _, [ t1; t2 ], _) ->
        let _, modvar = Map.Poly.find_exn map (t1, t2) in
        Var (modvar, T_int.SInt, Dummy)
    | FunApp (sym, args, info) ->
        let sym =
          match sym with
          | T_bool.Formula phi ->
              T_bool.Formula (Formula.replace_div_mod map phi)
          | sym -> sym
        in
        FunApp (sym, List.map args ~f:(replace_div_mod map), info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          (var, sort, replace_div_mod map def, replace_div_mod map body, info)

  let rec complete_tsort map = function
    | Var _ as t -> t
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp (T_bool.Formula (Formula.complete_tsort map phi), [], info)
    | FunApp (op, ts, info) ->
        FunApp (op, List.map ts ~f:(complete_tsort map), info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          (var, sort, complete_tsort map def, complete_tsort map body, info)

  let rec complete_psort map = function
    | Var _ as t -> t
    | FunApp (T_bool.Formula phi, [], info) ->
        FunApp (T_bool.Formula (Formula.complete_psort map phi), [], info)
    | FunApp (op, ts, info) ->
        FunApp (op, List.map ts ~f:(complete_psort map), info)
    | LetTerm (var, sort, def, body, info) ->
        LetTerm
          (var, sort, complete_psort map def, complete_psort map body, info)

  (** Unification and Pattern Matching *)

  let rec unify bvs t1 t2 =
    match (t1, t2) with
    | t1, t2 when Stdlib.(t1 = t2) -> Option.some @@ Map.Poly.empty
    | ( FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
        FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _) )
      when (Atom.is_true atm1 && Atom.is_true atm2)
           || (Atom.is_false atm1 && Atom.is_false atm2)
           (* ToDo: reachable? *) ->
        Option.some @@ Map.Poly.empty
    | Var (x, _, _), t when (not (Set.mem bvs x)) && not (Set.mem (tvs_of t) x)
      ->
        Option.some @@ Map.Poly.singleton x t
    | t, Var (x, _, _) when (not (Set.mem bvs x)) && not (Set.mem (tvs_of t) x)
      ->
        Option.some @@ Map.Poly.singleton x t
    | ( FunApp
          ( ((T_int.(Add | Sub) | T_real.(RAdd | RSub)) as fsym),
            [ Var (x, _, _); t3 ],
            _ ),
        t )
      when (not (Set.mem bvs x))
           && (not (Set.mem (tvs_of t3) x))
           && not (Set.mem (tvs_of t) x) ->
        Option.some
        @@ Map.Poly.singleton x (Term.mk_fsym_app (negate_fsym fsym) [ t; t3 ])
    | ( t,
        FunApp
          ( ((T_int.(Add | Sub) | T_real.(RAdd | RSub)) as fsym),
            [ Var (x, _, _); t3 ],
            _ ) )
      when (not (Set.mem bvs x))
           && (not (Set.mem (tvs_of t3) x))
           && not (Set.mem (tvs_of t) x) ->
        Option.some
        @@ Map.Poly.singleton x (Term.mk_fsym_app (negate_fsym fsym) [ t; t3 ])
    | FunApp (((T_int.Add | T_real.RAdd) as fsym), [ t3; Var (x, _, _) ], _), t
      when (not (Set.mem bvs x))
           && (not (Set.mem (tvs_of t3) x))
           && not (Set.mem (tvs_of t) x) ->
        Option.some
        @@ Map.Poly.singleton x (Term.mk_fsym_app (negate_fsym fsym) [ t; t3 ])
    | t, FunApp (((T_int.Add | T_real.RAdd) as fsym), [ t3; Var (x, _, _) ], _)
      when (not (Set.mem bvs x))
           && (not (Set.mem (tvs_of t3) x))
           && not (Set.mem (tvs_of t) x) ->
        Option.some
        @@ Map.Poly.singleton x (Term.mk_fsym_app (negate_fsym fsym) [ t; t3 ])
    | t, FunApp (((T_int.Sub | T_real.RSub) as fsym), [ t3; Var (x, _, _) ], _)
      when (not (Set.mem bvs x))
           && (not (Set.mem (tvs_of t3) x))
           && not (Set.mem (tvs_of t) x) ->
        Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app fsym [ t3; t ])
    | FunApp (((T_int.Sub | T_real.RSub) as fsym), [ t3; Var (x, _, _) ], _), t
      when (not (Set.mem bvs x))
           && (not (Set.mem (tvs_of t3) x))
           && not (Set.mem (tvs_of t) x) ->
        Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app fsym [ t3; t ])
    | ( FunApp ((T_dt.DTCons (_, _, _) as fsym1), ts1, _),
        FunApp ((T_dt.DTCons (_, _, _) as fsym2), ts2, _) )
      when Stdlib.(fsym1 = fsym2) ->
        List.fold2_exn ts1 ts2 ~init:(Some Map.Poly.empty) ~f:(fun opt t1 t2 ->
            match opt with
            | None -> None
            | Some opt -> (
                match unify bvs t1 t2 with
                | None -> None
                | Some opt' -> (
                    try
                      Some
                        (Map.force_merge opt
                           opt'
                           (*~catch_dup:(fun (tvar, t1, t2) ->
                               print_endline @@ sprintf "%s : %s != %s"
                                 (Ident.name_of_tvar tvar) (Term.str_of t1) (Term.str_of t2))*))
                    with _ -> None)))
    | _ -> None (* ToDo: remerdy incompleteness. support more general terms *)

  (* variables in t1 and t2 belong to different name spaces *)
  let pattern_match bvs t1 t2 =
    if (Set.is_empty @@ Term.tvs_of t1) && Stdlib.(t1 = t2) then
      Option.some @@ Map.Poly.empty
    else
      match (t1, t2) with
      | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _)
        when Z.Compare.( = ) n1 n2 ->
          (* ToDo: reachable? *)
          Option.some @@ Map.Poly.empty
      | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
        when Q.( = ) r1 r2 ->
          (* ToDo: reachable? *)
          Option.some @@ Map.Poly.empty
      | ( FunApp (T_bv.BVNum (size1, n1), [], _),
          FunApp (T_bv.BVNum (size2, n2), [], _) )
        when Stdlib.(size1 = size2) && Z.Compare.( = ) n1 n2 ->
          (* ToDo: reachable? *)
          Option.some @@ Map.Poly.empty
      | ( FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
          FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _) )
        when (Atom.is_true atm1 && Atom.is_true atm2)
             || (Atom.is_false atm1 && Atom.is_false atm2)
             (* ToDo: reachable? *) ->
          Option.some @@ Map.Poly.empty
      | Var (x, _, _), _ when not @@ Set.mem bvs x ->
          Option.some @@ Map.Poly.singleton x t2
      | FunApp ((T_int.(Add | Sub) as fsym), [ Var (x, _, _); t3 ], _), t
        when (not (Set.mem bvs x)) && (Set.is_empty @@ Term.tvs_of t3) ->
          Option.some
          @@ Map.Poly.singleton x
               (Term.mk_fsym_app (negate_fsym fsym) [ t; t3 ])
      | FunApp (T_int.Add, [ t3; Var (x, _, _) ], _), t
        when (not (Set.mem bvs x)) && (Set.is_empty @@ Term.tvs_of t3) ->
          Option.some
          @@ Map.Poly.singleton x (Term.mk_fsym_app T_int.Sub [ t; t3 ])
      | FunApp (T_int.Sub, [ t3; Var (x, _, _) ], _), t
        when (not (Set.mem bvs x)) && (Set.is_empty @@ Term.tvs_of t3) ->
          Option.some
          @@ Map.Poly.singleton x (Term.mk_fsym_app T_int.Sub [ t3; t ])
      | _ -> None
  (* ToDo: remerdy incompleteness. support more general terms *)
  (* especially, non-linear pattern is not supported *)
end

and Predicate :
  (Type.PredicateType
    with type formula := Formula.t
     and type formula_def := Formula.t Formula.def
     and type term := Term.t) = struct
  type fixpoint = Mu | Nu | Fix

  type t =
    | Var of pred_bind
    | Psym of pred_sym
    | Fixpoint of Formula.t Formula.def

  (** Construction *)

  let mk_var pvar sort = Var (pvar, sort)
  let mk_psym psym = Psym psym
  let mk_fix kind name args body = Fixpoint { kind; name; args; body }

  (** Destruction *)

  let let_var = function Var (pvar, sort) -> (pvar, sort) | _ -> assert false
  let let_psym = function Psym psym -> psym | _ -> assert false
  let let_fix = function Fixpoint def -> def | _ -> assert false

  (** Fixpoint Operators *)

  let str_of_fop = function Mu -> "mu" | Nu -> "nu" | Fix -> "fix"
  let flip_fop = function Mu -> Nu | Nu -> Mu | Fix -> Fix

  (** Predicate Symbols *)

  let is_infix_psym = function
    | T_bool.(Eq | Neq)
    | T_int.(Leq | Geq | Lt | Gt | PDiv | NotPDiv)
    | T_real.(RLeq | RGeq | RLt | RGt)
    | T_bv.(BVLeq _ | BVGeq _ | BVLt _ | BVGt _)
    | T_num.(NLeq _ | NGeq _ | NLt _ | NGt _) ->
        true
    | _ -> false

  let str_of_psym = function
    | T_bool.Eq -> "="
    | T_bool.Neq -> "!="
    | T_int.Leq -> "<="
    | T_int.Geq -> ">="
    | T_int.Lt -> "<"
    | T_int.Gt -> ">"
    | T_int.PDiv -> "|"
    | T_int.NotPDiv -> "!|"
    | T_real.RLeq -> "<=."
    | T_real.RGeq -> ">=."
    | T_real.RLt -> "<."
    | T_real.RGt -> ">."
    | T_bv.BVLeq (size, signed) ->
        sprintf "%sle%s" (T_bv.str_of_signed signed) (T_bv.str_of_size size)
    | T_bv.BVGeq (size, signed) ->
        sprintf "%sge%s" (T_bv.str_of_signed signed) (T_bv.str_of_size size)
    | T_bv.BVLt (size, signed) ->
        sprintf "%slt%s" (T_bv.str_of_signed signed) (T_bv.str_of_size size)
    | T_bv.BVGt (size, signed) ->
        sprintf "%sgt%s" (T_bv.str_of_signed signed) (T_bv.str_of_size size)
    | T_num.NLeq svar -> sprintf "<=_%s" (Ident.name_of_svar svar) (* "'<=" *)
    | T_num.NGeq svar -> sprintf ">=_%s" (Ident.name_of_svar svar) (* "'>=" *)
    | T_num.NLt svar -> sprintf "<_%s" (Ident.name_of_svar svar) (* "'<" *)
    | T_num.NGt svar -> sprintf ">_%s" (Ident.name_of_svar svar) (* "'>" *)
    | T_sequence.IsPrefix _fin -> "is_prefix"
    | T_sequence.NotIsPrefix _fin -> "not is_prefix"
    | T_sequence.SeqInRegExp (_fin, regexp) ->
        sprintf "in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | T_sequence.NotSeqInRegExp (_fin, regexp) ->
        sprintf "not in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | T_regex.StrInRegExp -> sprintf "str_in_regex"
    | T_regex.NotStrInRegExp -> sprintf "not str_in_regex"
    | T_tuple.IsTuple sorts ->
        sprintf "is_tuple(%s)"
        @@ String.concat_map_list ~sep:" * " sorts ~f:Term.str_of_sort
    | T_tuple.NotIsTuple sorts ->
        sprintf "is_not_tuple(%s)"
        @@ String.concat_map_list ~sep:" * " sorts ~f:Term.str_of_sort
    | T_dt.IsCons (name, _) -> sprintf "is_%s" name
    | T_dt.NotIsCons (name, _) -> sprintf "is_not_%s" name
    | _ -> failwith "unknown pred symbol"

  let subst_sorts_psym map = function
    | T_num.(NGt svar | NLt svar | NGeq svar | NLeq svar) as psym ->
        T_num.psym_of_num_psym psym
        @@ Term.subst_sorts_sort map @@ Sort.SVar svar
    | T_tuple.IsTuple sorts ->
        T_tuple.IsTuple (List.map ~f:(Term.subst_sorts_sort map) sorts)
    | T_tuple.NotIsTuple sorts ->
        T_tuple.NotIsTuple (List.map ~f:(Term.subst_sorts_sort map) sorts)
    | T_dt.IsCons (name, dt) -> T_dt.IsCons (name, Datatype.subst_sorts map dt)
    | T_dt.NotIsCons (name, dt) ->
        T_dt.NotIsCons (name, Datatype.subst_sorts map dt)
    | psym -> psym (* ToDo *)

  let subst_conts_psym map = function
    | T_num.(NGt svar | NLt svar | NGeq svar | NLeq svar) as psym ->
        T_num.psym_of_num_psym psym
        @@ Term.subst_conts_sort map @@ Sort.SVar svar
    | T_tuple.IsTuple sorts ->
        T_tuple.IsTuple (List.map ~f:(Term.subst_conts_sort map) sorts)
    | T_tuple.NotIsTuple sorts ->
        T_tuple.NotIsTuple (List.map ~f:(Term.subst_conts_sort map) sorts)
    | T_dt.IsCons (name, dt) -> T_dt.IsCons (name, Datatype.subst_conts map dt)
    | T_dt.NotIsCons (name, dt) ->
        T_dt.NotIsCons (name, Datatype.subst_conts map dt)
    | psym -> psym (* ToDo *)

  let subst_opsigs_psym map = function
    | T_num.(NGt svar | NLt svar | NGeq svar | NLeq svar) as psym ->
        T_num.psym_of_num_psym psym
        @@ Term.subst_opsigs_sort map @@ Sort.SVar svar
    | T_tuple.IsTuple sorts ->
        T_tuple.IsTuple (List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | T_tuple.NotIsTuple sorts ->
        T_tuple.NotIsTuple (List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | T_dt.IsCons (name, dt) -> T_dt.IsCons (name, Datatype.subst_opsigs map dt)
    | T_dt.NotIsCons (name, dt) ->
        T_dt.NotIsCons (name, Datatype.subst_opsigs map dt)
    | psym -> psym (* ToDo *)

  let is_flippable_psym = function
    | T_bool.(Eq | Neq)
    | T_int.(Leq | Geq | Lt | Gt)
    | T_real.(RLeq | RGeq | RLt | RGt)
    | T_bv.(BVLeq (_, _) | BVGeq (_, _) | BVLt (_, _) | BVGt (_, _))
    | T_num.(NLeq _ | NGeq _ | NLt _ | NGt _) ->
        true
    | _ -> false

  let is_included_psym psym1 psym2 =
    match (psym1, psym2) with
    | T_bool.Eq, T_bool.Eq
    | T_bool.Eq, T_int.Leq
    | T_bool.Eq, T_int.Geq
    | T_bool.Eq, T_real.RLeq
    | T_bool.Eq, T_real.RGeq
    | T_bool.Eq, T_bv.BVLeq (_, _)
    | T_bool.Eq, T_bv.BVGeq (_, _)
    | T_bool.Eq, T_num.NLeq _
    | T_bool.Eq, T_num.NGeq _
    | T_bool.Neq, T_bool.Neq
    | T_int.Lt, T_bool.Neq
    | T_int.Gt, T_bool.Neq
    | T_real.RLt, T_bool.Neq
    | T_real.RGt, T_bool.Neq
    | T_int.Leq, T_int.Leq
    | T_int.Geq, T_int.Geq
    | T_int.Lt, T_int.Lt
    | T_int.Lt, T_int.Leq
    | T_int.Gt, T_int.Gt
    | T_int.Gt, T_int.Geq
    | T_real.RLeq, T_real.RLeq
    | T_real.RGeq, T_real.RGeq
    | T_real.RLt, T_real.RLt
    | T_real.RLt, T_real.RLeq
    | T_real.RGt, T_real.RGt
    | T_real.RGt, T_real.RGeq ->
        true
    | T_bv.BVLeq (size1, signed1), T_bv.BVLeq (size2, signed2)
    | T_bv.BVGeq (size1, signed1), T_bv.BVGeq (size2, signed2)
    | T_bv.BVLt (size1, signed1), T_bv.BVLt (size2, signed2)
    | T_bv.BVLt (size1, signed1), T_bv.BVLeq (size2, signed2)
    | T_bv.BVGt (size1, signed1), T_bv.BVGt (size2, signed2)
    | T_bv.BVGt (size1, signed1), T_bv.BVGeq (size2, signed2) ->
        Stdlib.(size1 = size2 && signed1 = signed2)
    | T_num.NLeq sort1, T_num.NLeq sort2
    | T_num.NGeq sort1, T_num.NGeq sort2
    | T_num.NLt sort1, T_num.NLt sort2
    | T_num.NLt sort1, T_num.NLeq sort2
    | T_num.NGt sort1, T_num.NGt sort2
    | T_num.NGt sort1, T_num.NGeq sort2 ->
        Stdlib.(sort1 = sort2)
    | _ -> false

  let flip_psym = function
    | T_bool.Eq -> T_bool.Eq
    | T_bool.Neq -> T_bool.Neq
    | T_int.Leq -> T_int.Geq
    | T_int.Geq -> T_int.Leq
    | T_int.Lt -> T_int.Gt
    | T_int.Gt -> T_int.Lt
    | T_real.RLeq -> T_real.RGeq
    | T_real.RGeq -> T_real.RLeq
    | T_real.RLt -> T_real.RGt
    | T_real.RGt -> T_real.RLt
    | T_bv.BVLeq (size, signed) -> T_bv.BVGeq (size, signed)
    | T_bv.BVGeq (size, signed) -> T_bv.BVLeq (size, signed)
    | T_bv.BVLt (size, signed) -> T_bv.BVGt (size, signed)
    | T_bv.BVGt (size, signed) -> T_bv.BVLt (size, signed)
    | T_num.NLeq sort -> T_num.NGeq sort
    | T_num.NGeq sort -> T_num.NLeq sort
    | T_num.NLt sort -> T_num.NGt sort
    | T_num.NGt sort -> T_num.NLt sort
    | psym -> failwith ("[flip_psym] not supported: " ^ str_of_psym psym)

  let is_negatable_psym = function
    | T_bool.(Eq | Neq)
    | T_int.(Leq | Geq | Lt | Gt | PDiv | NotPDiv)
    | T_real.(RLeq | RGeq | RLt | RGt)
    | T_bv.(BVLeq (_, _) | BVGeq (_, _) | BVLt (_, _) | BVGt (_, _))
    | T_num.(NLeq _ | NGeq _ | NLt _ | NGt _)
    | T_sequence.(
        IsPrefix _ | NotIsPrefix _ | SeqInRegExp (_, _) | NotSeqInRegExp (_, _))
    | T_regex.(StrInRegExp | NotStrInRegExp)
    | T_tuple.(IsTuple _ | NotIsTuple _)
    | T_dt.(IsCons (_, _) | NotIsCons (_, _)) ->
        true
    | _ -> false

  let negate_psym = function
    | T_bool.Eq -> T_bool.Neq
    | T_bool.Neq -> T_bool.Eq
    | T_int.Leq -> T_int.Gt
    | T_int.Geq -> T_int.Lt
    | T_int.Lt -> T_int.Geq
    | T_int.Gt -> T_int.Leq
    | T_int.PDiv -> T_int.NotPDiv
    | T_int.NotPDiv -> T_int.PDiv
    | T_real.RLeq -> T_real.RGt
    | T_real.RGeq -> T_real.RLt
    | T_real.RLt -> T_real.RGeq
    | T_real.RGt -> T_real.RLeq
    | T_bv.BVLeq (size, signed) -> T_bv.BVGt (size, signed)
    | T_bv.BVGeq (size, signed) -> T_bv.BVLt (size, signed)
    | T_bv.BVLt (size, signed) -> T_bv.BVGeq (size, signed)
    | T_bv.BVGt (size, signed) -> T_bv.BVLeq (size, signed)
    | T_irb.IsInt -> failwith "[negate_psym] not supported"
    | T_num.NLeq sort -> T_num.NGt sort
    | T_num.NGeq sort -> T_num.NLt sort
    | T_num.NLt sort -> T_num.NGeq sort
    | T_num.NGt sort -> T_num.NLeq sort
    | T_sequence.IsPrefix fin -> T_sequence.NotIsPrefix fin
    | T_sequence.NotIsPrefix fin -> T_sequence.IsPrefix fin
    | T_sequence.SeqInRegExp (fin, regexp) ->
        T_sequence.NotSeqInRegExp (fin, regexp)
    | T_sequence.NotSeqInRegExp (fin, regexp) ->
        T_sequence.SeqInRegExp (fin, regexp)
    | T_regex.StrInRegExp -> T_regex.NotStrInRegExp
    | T_regex.NotStrInRegExp -> T_regex.StrInRegExp
    | T_tuple.IsTuple sorts -> T_tuple.NotIsTuple sorts
    | T_tuple.NotIsTuple sorts -> T_tuple.IsTuple sorts
    | T_dt.IsCons (name, dt) -> T_dt.NotIsCons (name, dt)
    | T_dt.NotIsCons (name, dt) -> T_dt.IsCons (name, dt)
    | psym -> failwith ("[negate_psym] not supported: " ^ str_of_psym psym)

  (** Printing *)

  let str_of = function
    | Var (Ident.Pvar pvar, _sorts) -> pvar
    (* sprintf "(%s : [%s])" pvar
       (String.concat_map_list ~sep:";" ~f:Term.str_of_sort sorts) *)
    | Psym psym -> str_of_psym psym
    | Fixpoint def ->
        sprintf "(%s%s%s. %s)" (str_of_fop def.kind)
          (Ident.name_of_pvar def.name)
          (String.paren @@ str_of_sort_env_list Term.str_of_sort def.args)
          (Formula.str_of ~priority:Priority.lowest def.body)

  (** Observation *)

  let is_var = function Var _ -> true | _ -> false
  let is_psym = function Psym _ -> true | _ -> false
  let is_fix = function Fixpoint _ -> true | _ -> false

  let tvs_of = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint def ->
        Set.diff (Formula.tvs_of def.body)
          (Set.add
             (Set.Poly.of_list @@ List.map ~f:fst def.args)
             (Ident.pvar_to_tvar def.name))

  let pvs_of = function
    | Var (pvar, _) -> Set.Poly.singleton pvar
    | Psym _ -> Set.Poly.empty
    | Fixpoint def ->
        Set.diff (Formula.pvs_of def.body)
          (Set.add
             (Set.Poly.map ~f:Ident.tvar_to_pvar
             @@ Set.Poly.of_list @@ List.map ~f:fst def.args)
             def.name)

  let fvs_of atm =
    Set.union (tvs_of atm)
      (Set.Poly.map ~f:Ident.pvar_to_tvar (*ToDo*) @@ pvs_of atm)

  let svs_of = function
    | Var (_, sorts) ->
        Set.Poly.of_list
        @@ List.filter_map sorts ~f:(function
             | Sort.SVar svar -> Some svar
             | _ -> None)
    | Psym _ -> Set.Poly.empty
    | Fixpoint def ->
        Set.union (Formula.svs_of def.body)
          (Set.Poly.of_list
          @@ List.filter_map ~f:(function
               | Sort.SVar svar -> Some svar
               | _ -> None)
          @@ List.map ~f:snd def.args)

  let term_sort_env_of ?(bvs = Set.Poly.empty) = function
    | Var _ | Psym _ -> Set.Poly.empty
    | Fixpoint def ->
        Set.diff
          (Formula.term_sort_env_of ~bvs def.body)
          (Set.Poly.of_list def.args)

  let pred_sort_env_of ?(bpvs = Set.Poly.empty) = function
    | Var (pvar, sorts) ->
        if Set.mem bpvs pvar then Set.Poly.empty
        else Set.Poly.singleton (pvar, sorts)
    | Psym _ -> Set.Poly.empty
    | Fixpoint def ->
        Formula.pred_sort_env_of ~bpvs:(Set.add bpvs def.name) def.body

  let sort_env_of ?(bpvs = Set.Poly.empty) pred =
    Set.union (term_sort_env_of pred)
      (Term.pred_to_sort_env @@ pred_sort_env_of ~bpvs pred)

  let terms_of = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint def -> Formula.terms_of def.body

  let fvar_apps_of = function
    | Var (_, _) -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint def -> Formula.fvar_apps_of def.body

  let nesting_level = function
    | Fixpoint def -> 1 + Formula.nesting_level def.body
    | _ -> 0

  let number_of_quantifiers = function
    | Fixpoint def -> Formula.number_of_quantifiers def.body
    | _ -> 0

  let funsyms_of = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint def -> Formula.funsyms_of def.body

  let predsyms_of = function
    | Var _ -> Set.Poly.empty
    | Psym psym -> Set.Poly.singleton psym
    | Fixpoint def -> Formula.predsyms_of def.body

  (** Substitution *)

  let rename map = function
    | Var (pvar, sort) -> (
        match Map.Poly.find map (Ident.pvar_to_tvar pvar (*ToDo*)) with
        | None -> Var (pvar, sort)
        | Some tvar -> Var (Ident.tvar_to_pvar tvar, sort))
    | Psym sym -> Psym sym
    | Fixpoint def ->
        let map' = Map.remove_keys map (List.map ~f:fst def.args) in
        Fixpoint { def with body = Formula.rename map' def.body }

  let rename_pvars map = function
    | Var (pvar, sorts) -> (
        match Map.Poly.find map pvar with
        | None -> Var (pvar, sorts)
        | Some pvar' -> Var (pvar', sorts))
    | Psym sym -> Psym sym
    | Fixpoint def ->
        let map' = Map.Poly.remove map def.name in
        Fixpoint { def with body = Formula.rename_pvars map' def.body }

  let rename_sorted_pvars map = function
    | Var (pvar, sorts) -> (
        match Map.Poly.find map (Ident.name_of_pvar pvar, sorts) with
        | None -> Var (pvar, sorts)
        | Some pvar' -> Var (pvar', sorts))
    | Psym sym -> Psym sym
    | Fixpoint def ->
        let map' =
          Map.Poly.remove map
            (Ident.name_of_pvar def.name, List.map def.args ~f:snd)
        in
        Fixpoint { def with body = Formula.rename_sorted_pvars map' def.body }

  let subst_neg pvar = function
    | Var (pvar', sort) ->
        if Stdlib.(pvar = pvar') then
          assert false (* it must be handled with Formula.subst_neg *)
        else Var (pvar', sort)
    | Psym psym -> Psym psym
    | Fixpoint def ->
        if Stdlib.(pvar = def.name) then assert false
        else Fixpoint { def with body = Formula.subst_neg pvar def.body }

  let subst_sorts map = function
    | Var (pvar, sorts) ->
        Var (pvar, List.map ~f:(Term.subst_sorts_sort map) sorts)
    | Psym psym -> Psym (subst_sorts_psym map psym)
    | Fixpoint def ->
        Fixpoint
          {
            def with
            args = Formula.subst_sorts_bounds map def.args;
            body = Formula.subst_sorts map def.body;
          }

  let subst_conts map = function
    | Var (pvar, sorts) ->
        Var (pvar, List.map ~f:(Term.subst_conts_sort map) sorts)
    | Psym psym -> Psym (subst_conts_psym map psym)
    | Fixpoint def ->
        Fixpoint
          {
            def with
            args = Formula.subst_conts_bounds map def.args;
            body = Formula.subst_conts map def.body;
          }

  let subst_opsigs map = function
    | Var (pvar, sorts) ->
        Var (pvar, List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | Psym psym -> Psym (subst_opsigs_psym map psym)
    | Fixpoint def ->
        Fixpoint
          {
            def with
            args = Formula.subst_opsigs_bounds map def.args;
            body = Formula.subst_opsigs map def.body;
          }

  let aconv_tvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint def ->
        let args, map = refresh_sort_env_list def.args in
        Fixpoint
          {
            def with
            args;
            body = Formula.rename map @@ Formula.aconv_tvar def.body;
          }

  let aconv_tvar_norm next = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint def ->
        let args, map = refresh_sort_env_list_norm next def.args in
        Fixpoint
          {
            def with
            args;
            body = Formula.rename map @@ Formula.aconv_tvar_norm next def.body;
          }

  let aconv_pvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint def ->
        let name = Ident.mk_fresh_pvar () in
        Fixpoint
          {
            def with
            name;
            body =
              Formula.aconv_pvar
              @@ Formula.rename_pvars
                   (Map.Poly.singleton def.name name)
                   def.body;
          }

  (** Transformation *)

  let negate ?(negate_formula = Formula.mk_neg ~info:Dummy) = function
    | Var _ -> None
    | Fixpoint def ->
        Option.return
        @@ Fixpoint
             {
               def with
               kind = flip_fop def.kind;
               body = negate_formula def.body;
             }
    | Psym psym -> (
        try Option.return (Psym (negate_psym psym)) with _ -> None)

  let complete_psort map = function
    | Var (pvar, _) -> (
        match Map.Poly.find map pvar with
        | Some sorts -> Var (pvar, sorts)
        | None -> failwith @@ "not found " ^ Ident.name_of_pvar pvar)
    | pred -> pred

  let extend_pred_params x extended_params = function
    | Fixpoint def ->
        Fixpoint
          {
            def with
            body = Formula.extend_pred_params x extended_params def.body;
          }
    | x -> x
end

and Atom :
  (Type.AtomType
    with type predicate := Predicate.t
     and type term := Term.t
     and type formula := Formula.t
     and type termSubst := TermSubst.t
     and type predSubst := PredSubst.t
     and type funcSubst := FuncSubst.t) = struct
  type t =
    | True of info
    | False of info
    | App of Predicate.t * Term.t list * info

  (** Construction *)

  let mk_true ?(info = Dummy) () = True info
  let mk_false ?(info = Dummy) () = False info
  let mk_bool b = if b then mk_true () else mk_false ()
  let mk_app ?(info = Dummy) pred args = App (pred, args, info)
  let mk_psym_app ?(info = Dummy) psym = mk_app ~info (Predicate.mk_psym psym)

  let mk_pvar_app ?(info = Dummy) pvar sorts =
    mk_app ~info (Predicate.mk_var pvar sorts)

  let pvar_app_of_senv ?(info = Dummy) pvar senv =
    mk_pvar_app ~info pvar (List.map ~f:snd senv) (Term.of_sort_env senv)

  let of_bool_var b =
    T_bool.mk_eq (Term.mk_var b T_bool.SBool) (T_bool.mk_true ())

  let of_bool_term = function
    | Term.Var (b, T_bool.SBool, _) -> of_bool_var b
    | t ->
        (*ToDo: check that [t] is a boolean term*)
        T_bool.mk_eq t (T_bool.mk_true ())

  let of_neg_bool_var b =
    T_bool.mk_eq (Term.mk_var b T_bool.SBool) (T_bool.mk_false ())

  let of_neg_bool_term = function
    | Term.Var (b, T_bool.SBool, _) -> of_neg_bool_var b
    | t ->
        (*ToDo: check that [t] is a boolean term*)
        T_bool.mk_eq t (T_bool.mk_false ())

  let insert_let_pvar_app var sort def info atom =
    let x, sorts, ts, _ = Atom.let_pvar_app atom in
    Atom.mk_pvar_app ~info x sorts
    @@ List.map ts ~f:(Term.insert_let_term var sort def info)

  (** Destruction *)

  let let_app = function
    | App (pred, args, info) -> (pred, args, info)
    | _ -> assert false

  let let_psym_app = function
    | App (Predicate.Psym sym, args, info) -> (sym, args, info)
    | _ -> assert false

  let let_pvar_app = function
    | App (Predicate.Var (pvar, sorts), args, info) -> (pvar, sorts, args, info)
    | _ -> assert false

  let info_of_true = function True info -> info | _ -> assert false
  let info_of_false = function False info -> info | _ -> assert false

  let info_of = function
    | True info -> info
    | False info -> info
    | App (_, _, info) -> info

  let pvar_of = function
    | App (Predicate.Var (pvar, _), _, _) -> pvar
    | _ -> assert false

  (** Morphism *)

  let map_term ~f = function
    | (True _ | False _) as atom -> atom
    | App (pred, args, info) ->
        App (pred, List.map args ~f:(Term.map_term true ~f), info)

  let iter_term ~f t =
    let _ =
      map_term t ~f:(fun t ->
          f t;
          t)
    in
    ()

  (** Printing *)

  let str_of ?(priority = Priority.lowest) = function
    | True _ -> "true"
    | False _ -> "false"
    | App (Predicate.Psym psym, [ t1; t2 ], _) when Predicate.is_infix_psym psym
      ->
        Priority.add_paren priority Priority.eq_neq_lt_leq_gt_geq
        @@ sprintf "%s %s %s"
             (Term.str_of ~priority:(Priority.eq_neq_lt_leq_gt_geq + 1) t1)
             (Predicate.str_of_psym psym)
             (Term.str_of ~priority:(Priority.eq_neq_lt_leq_gt_geq + 1) t2)
    | App (pred, args, _) ->
        if List.length args = 0 then Predicate.str_of pred
        else
          Priority.add_paren priority Priority.fun_app
          @@ sprintf "%s %s" (Predicate.str_of pred)
               (String.concat_map_list ~sep:" " args
                  ~f:(Term.str_of ~priority:(Priority.fun_app + 1)))

  (** Observation *)

  let is_true = function True _ -> true | _ -> false
  let is_false = function False _ -> true | _ -> false
  let is_app = function App (_, _, _) -> true | _ -> false
  let is_psym_app = function App (Predicate.Psym _, _, _) -> true | _ -> false
  let is_pvar_app = function App (Predicate.Var _, _, _) -> true | _ -> false

  let is_pvar_app_of pvar = function
    | App (Predicate.Var (pvar', _), _, _) -> Stdlib.(pvar = pvar')
    | _ -> false

  let is_let_free = function
    | App (_, args, _) -> List.for_all args ~f:Term.is_let_free
    | _ -> true

  let is_quantifier_free = function
    | App (_, args, _) -> List.for_all args ~f:Term.is_quantifier_free
    | _ -> true

  let tvs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
        Set.Poly.union_list
          (Predicate.tvs_of pred :: List.map args ~f:Term.tvs_of)

  let pvs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
        Set.Poly.union_list
          (Predicate.pvs_of pred :: List.map args ~f:Term.pvs_of)

  let fvs_of atm =
    Set.union (tvs_of atm)
    @@ Set.Poly.map ~f:Ident.pvar_to_tvar
    (*ToDo*) @@ pvs_of atm

  let svs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
        Set.Poly.union_list
          (Predicate.svs_of pred :: List.map args ~f:Term.svs_of)

  let term_sort_env_of ?(bvs = Set.Poly.empty) = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
        Set.Poly.union_list
        @@ Predicate.term_sort_env_of ~bvs pred
           :: List.map args ~f:(Term.term_sort_env_of ~bvs)

  let pred_sort_env_of ?(bpvs = Set.Poly.empty) = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
        Set.Poly.union_list
        @@ Predicate.pred_sort_env_of ~bpvs pred
           :: List.map args ~f:(Term.pred_sort_env_of ~bpvs)

  let sort_env_of ?(bpvs = Set.Poly.empty) atm =
    Set.union (term_sort_env_of atm)
    @@ Term.pred_to_sort_env @@ pred_sort_env_of ~bpvs atm

  let occur pv atom = Set.mem (pvs_of atom) pv

  let funsyms_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, terms, _) ->
        Set.Poly.union_list
          (Predicate.funsyms_of pred :: List.map ~f:Term.funsyms_of terms)

  let predsyms_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, terms, _) ->
        Set.Poly.union_list
          (Predicate.predsyms_of pred :: List.map ~f:Term.predsyms_of terms)

  let pathexps_of ?(bvs = Set.Poly.empty) = function
    | True _ | False _ -> Set.Poly.empty
    | App (Predicate.Fixpoint def, args, _) ->
        Set.Poly.union_list
        @@ Set.diff
             (Formula.pathexps_of ~bvs def.body)
             (Set.Poly.of_list @@ Term.of_sort_env def.args)
           :: List.map args ~f:(Term.pathexps_of ~bvs)
    | App (_, args, _) ->
        Set.Poly.union_list @@ List.map args ~f:(Term.pathexps_of ~bvs)

  let filtered_terms_of ~f = function
    | True _ | False _ -> Set.Poly.empty
    | App (Predicate.Fixpoint def, args, _) ->
        Set.Poly.union_list
        @@ Formula.filtered_terms_of ~f def.body
           :: List.map args ~f:(Term.filtered_terms_of ~f)
    | App (_, args, _) ->
        Set.Poly.union_list @@ List.map args ~f:(Term.filtered_terms_of ~f)

  let terms_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, terms, _) ->
        Set.union (Predicate.terms_of pred) (Set.Poly.of_list terms)

  let fvar_apps_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, terms, _) ->
        Set.Poly.union_list
          (Predicate.fvar_apps_of pred :: List.map ~f:Term.fvar_apps_of terms)

  let atoms_of ?(pos = true) = function
    | True _ | False _ -> (Set.Poly.empty, Set.Poly.empty)
    | App (_pred (*ToDo*), terms, _) as atom ->
        let poss1, negs1 =
          List.unzip @@ List.map terms ~f:(Term.atoms_of ~pos)
        in
        if pos then
          ( Set.Poly.union_list (Set.Poly.singleton atom :: poss1),
            Set.Poly.union_list negs1 )
        else
          ( Set.Poly.union_list poss1,
            Set.Poly.union_list (Set.Poly.singleton atom :: negs1) )

  let nesting_level = function
    | True _ | False _ -> 0
    | App (pred, _, _) -> Predicate.nesting_level pred

  let number_of_quantifiers = function
    | True _ | False _ -> 0
    | App (pred, _, _) -> Predicate.number_of_quantifiers pred

  let number_of_pvar_apps ?(ex = Map.Poly.empty) is_pos = function
    | True _ | False _ -> 0
    | App (Predicate.Var _, [], _) -> 0
    | App (Predicate.Var _, _, _) -> if is_pos then 1 else 0
    | App (Predicate.Psym _, _, _) -> 0
    | App (Predicate.Fixpoint _, _, _) ->
        ignore ex;
        assert false
  (* This function does not support fixpoint fomulas appropriately *)

  let count_pvar_apps = function
    | True _ | False _ -> []
    | App (Predicate.Var (pvar, _), _, _) -> [ (pvar, (1, 0)) ]
    | App (Predicate.Psym _, _, _) -> []
    | App (Predicate.Fixpoint _, _, _) -> assert false

  let ast_size = function
    | True _ | False _ -> 1
    | App (Predicate.(Var _ | Psym _), terms, _) ->
        1 + (Integer.sum_list @@ List.map ~f:Term.ast_size terms)
    | App (Predicate.Fixpoint def, terms, _) ->
        1 + Formula.ast_size def.body
        + (Integer.sum_list @@ List.map ~f:Term.ast_size terms)

  let occur_times ?(map = Map.Poly.empty) x = function
    | True _ | False _ -> 0
    | App (_, ts, _) ->
        Integer.sum_list @@ List.map ~f:(Term.occur_times ~map x) ts

  (* assume that the argument is alpha-renamed *)
  let let_env_of ?(map = Map.Poly.empty) = function
    | App (_, args, _) ->
        List.fold args ~init:map ~f:(fun map -> Term.let_env_of ~map)
    | _ -> map

  (* assume that the argument is alpha-renamed *)
  let let_sort_env_of ?(map = Map.Poly.empty) = function
    | App (_, args, _) ->
        List.fold args ~init:map ~f:(fun map -> Term.let_sort_env_of ~map)
    | _ -> map

  let div_rem_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (_, args, _) ->
        Set.Poly.union_list @@ List.map ~f:Term.div_rem_of args

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
        App
          ( Predicate.rename_pvars map pred,
            List.map args ~f:(Term.rename_pvars map),
            info )

  let rename_sorted_pvars map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App
          ( Predicate.rename_sorted_pvars map pred,
            List.map args ~f:(Term.rename_sorted_pvars map),
            info )

  let alpha_rename_let ?(map = Map.Poly.empty) = function
    | App (pred, [], info) -> App (Predicate.rename map pred, [], info)
    | App (pred, ts, info) ->
        App (pred, List.map ts ~f:(Term.alpha_rename_let ~map), info)
    | atom -> atom

  let refresh_tvar (senv, atm) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ()) in
    (Map.rename_keys_map map senv, rename map atm)

  let subst map = function
    | True info -> Atom.mk_true () ~info
    | False info -> Atom.mk_false () ~info
    | App (Var (pvar, []), [], _)
      when Map.Poly.mem map (Ident.pvar_to_tvar pvar) ->
        Atom.of_bool_term @@ Map.Poly.find_exn map (Ident.pvar_to_tvar pvar)
    | App (Var (pvar, sorts), args, info) ->
        App (Var (pvar, sorts), List.map ~f:(Term.subst map) args, info)
    | App (Psym sym, args, info) ->
        App (Psym sym, List.map ~f:(Term.subst map) args, info)
    | App (Fixpoint def, args, info) ->
        let map' = Map.remove_keys map (List.map ~f:fst def.args) in
        App
          ( Fixpoint { def with body = Formula.subst map' def.body },
            List.map ~f:(Term.subst map') args,
            info )

  let subst_preds psub = function
    | True info -> Formula.mk_true ~info ()
    | False info -> Formula.mk_false ~info ()
    | App (pred, args, info) -> (
        let args = List.map ~f:(Term.subst_preds psub) args in
        match pred with
        | Predicate.Var (pvar, sort) -> (
            match Map.Poly.find psub pvar with
            | Some (senv, phi) ->
                let tsub =
                  TermSubst.make ~name:(Ident.name_of_pvar pvar) senv args
                in
                Formula.subst tsub phi
            | None ->
                Formula.mk_atom ~info (Atom.mk_pvar_app ~info pvar sort args))
        | Predicate.Psym psym ->
            Formula.mk_atom ~info (Atom.mk_psym_app ~info psym args)
        | Predicate.Fixpoint def ->
            Formula.mk_atom ~info
              (Atom.mk_app ~info
                 (Predicate.Fixpoint
                    {
                      def with
                      body =
                        Formula.subst_preds
                          (Map.Poly.remove psub def.name)
                          def.body;
                    })
                 args))

  let subst_funcs fsub = function
    | True info -> Atom.mk_true ~info ()
    | False info -> Atom.mk_false ~info ()
    | App (pred, args, info) ->
        let pred =
          match pred with
          | Predicate.Fixpoint def ->
              Predicate.Fixpoint
                { def with body = Formula.subst_funcs fsub (*ToDo*) def.body }
          | _ -> pred
        in
        Atom.mk_app ~info pred (List.map ~f:(Term.subst_funcs fsub) args)

  let subst_neg pvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) -> App (Predicate.subst_neg pvar pred, args, info)

  let subst_sorts map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App
          ( Predicate.subst_sorts map pred,
            List.map ~f:(Term.subst_sorts map) args,
            info )

  let subst_conts map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App
          ( Predicate.subst_conts map pred,
            List.map ~f:(Term.subst_conts map) args,
            info )

  let subst_opsigs map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App
          ( Predicate.subst_opsigs map pred,
            List.map ~f:(Term.subst_opsigs map) args,
            info )

  let aconv_tvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App (Predicate.aconv_tvar pred, List.map ~f:Term.aconv_tvar args, info)

  let aconv_tvar_norm next = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App
          ( Predicate.aconv_tvar_norm next pred,
            List.map ~f:(Term.aconv_tvar_norm next) args,
            info )

  let aconv_pvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App (Predicate.aconv_pvar pred, List.map ~f:Term.aconv_pvar args, info)

  (** Transformation *)

  let negate ?(negate_formula = Formula.mk_neg ~info:Dummy) = function
    | True info -> Option.return @@ False info
    | False info -> Option.return @@ True info
    | App (pred, args, info) -> (
        match Predicate.negate ~negate_formula pred with
        | None -> None
        | Some neg_pred -> Option.return @@ App (neg_pred, args, info))

  let complete_psort map = function
    | True info -> True info
    | False info -> False info
    | App (pred, terms, info) ->
        App (Predicate.complete_psort map pred, terms, info)

  let elim_neq = function
    | App (Psym T_bool.Neq, [ t1; t2 ], _) ->
        Formula.mk_neg @@ Formula.eq (Term.elim_neq t1) (Term.elim_neq t2)
    | App (pred, terms, info) ->
        Formula.mk_atom @@ App (pred, List.map ~f:Term.elim_neq terms, info)
    | atm -> Formula.mk_atom atm

  let elim_ite = function
    | App
        ( Psym
            (( T_bool.(Eq | Neq)
             | T_int.(Leq | Geq | Lt | Gt)
             | T_real.(RLeq | RGeq | RLt | RGt)
             | T_bv.(BVLeq _ | BVGeq _ | BVLt _ | BVGt _) ) as psym),
          [ t1; t2 ],
          _ ) ->
        List.cartesian_product (Term.elim_ite t1) (Term.elim_ite t2)
        |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
               Formula.and_of
                 [
                   phi1;
                   phi2;
                   Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ];
                 ])
        |> Formula.or_of
    | App (pred, [ t ], _) ->
        Term.elim_ite t
        |> List.map ~f:(fun (phi, t) ->
               Formula.and_of [ phi; Formula.mk_atom @@ Atom.mk_app pred [ t ] ])
        |> Formula.or_of
    | atm -> Formula.mk_atom atm

  let elim_false phi =
    (*ToDo: for PolyQEnt *)
    if Formula.is_false phi then Formula.eq (T_real.rzero ()) (T_real.rone ())
    else phi

  let elim_ite_prob simplify = function
    | App
        ( Psym
            (( T_bool.(Eq | Neq)
             | T_int.(Leq | Geq | Lt | Gt)
             | T_real.(RLeq | RGeq | RLt | RGt)
             | T_bv.(BVLeq _ | BVGeq _ | BVLt _ | BVGt _) ) as psym),
          [ t1; t2 ],
          _ ) ->
        List.cartesian_product (Term.elim_ite t1) (Term.elim_ite t2)
        |> List.filter_map ~f:(fun ((phi1, t1), (phi2, t2)) ->
               let cond = simplify @@ Formula.and_of [ phi1; phi2 ] in
               let conc =
                 simplify @@ Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ]
               in
               if Formula.is_true conc || Formula.is_false cond then None
               else if Formula.is_true cond then Some (elim_false conc)
               else if Formula.is_false conc then
                 let neg_cond = Formula.negate cond in
                 if Formula.is_atom neg_cond then Some neg_cond
                 else Some (Formula.mk_imply cond (elim_false conc))
               else Some (Formula.mk_imply cond conc))
        |> Set.Poly.of_list
    | App (pred, [ t ], _) ->
        Term.elim_ite t
        |> List.filter_map ~f:(fun (phi, t) ->
               let cond = simplify phi in
               let conc =
                 simplify @@ Formula.mk_atom @@ Atom.mk_app pred [ t ]
               in
               if Formula.is_true conc || Formula.is_false cond then None
               else if Formula.is_true cond then Some (elim_false conc)
               else if Formula.is_false conc then
                 let neg_cond = Formula.negate cond in
                 if Formula.is_atom neg_cond then Some neg_cond
                 else Some (Formula.mk_imply cond (elim_false conc))
               else Some (Formula.mk_imply cond conc))
        |> Set.Poly.of_list
    | atm ->
        let conc = simplify @@ Formula.mk_atom atm in
        if Formula.is_true conc then Set.Poly.empty
        else Set.Poly.singleton (elim_false conc)

  let instantiate_div0_mod0 = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App (pred, List.map args ~f:Term.instantiate_div0_mod0, info)

  let replace_div_mod map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
        App (pred, List.map args ~f:(Term.replace_div_mod map), info)

  let extend_pred_params pvar (extended_params : sort_env_list) = function
    | App (Predicate.Var (pvar', params), args, info) when Stdlib.(pvar = pvar')
      ->
        let extended_sorts : Sort.t list = List.map ~f:snd extended_params in
        let params = params @ extended_sorts in
        let extended_args = Term.of_sort_env extended_params in
        let args = args @ extended_args in
        App (Predicate.Var (pvar, params), args, info)
    | App (pred, args, info) ->
        let pred = Predicate.extend_pred_params pvar extended_params pred in
        let args =
          List.map ~f:(Term.extend_pred_params pvar extended_params) args
        in
        App (pred, args, info)
    | x -> x

  let instantiate atom =
    if is_pvar_app atom then
      map_term atom ~f:(function
        | Term.Var (var, sort, _) as term ->
            if Ident.is_dontcare var then Term.mk_dummy sort
            else
              (*print_endline (Term.str_of term);*)
              (* [var] is let-bound variable *)
              term
        | t -> t)
    else atom

  (** Unification and Pattern Matching *)

  let unify bvs atom1 atom2 =
    match (atom1, atom2) with
    | True _, True _ | False _, False _ -> Some Map.Poly.empty
    | App (pred1, ts1, _), App (pred2, ts2, _)
      when Stdlib.(pred1 = pred2) && List.length ts1 = List.length ts2 ->
        List.fold2_exn ts1 ts2 ~init:(Some Map.Poly.empty) ~f:(fun opt t1 t2 ->
            Option.(
              opt >>= fun map ->
              match Term.unify bvs (Term.subst map t1) (Term.subst map t2) with
              | Some theta -> (
                  try
                    Some
                      (Map.force_merge theta
                         (Map.Poly.map map ~f:(Term.subst theta))
                         (*~catch_dup:(fun (tvar, t1, t2) ->
                           print_endline @@ sprintf "%s : %s != %s"
                             (Ident.name_of_tvar tvar) (Term.str_of t1) (Term.str_of t2))*))
                  with _ -> None)
              | None -> None))
    | _ -> None

  let pattern_match bvs atom1 atom2 =
    match (atom1, atom2) with
    | True _, True _ | False _, False _ -> Some Map.Poly.empty
    | App (pred1, ts1, _), App (pred2, ts2, _)
      when Stdlib.(pred1 = pred2) && List.length ts1 = List.length ts2 -> (
        try
          List.fold2_exn ts1 ts2 ~init:(Some Map.Poly.empty)
            ~f:(fun opt t1 t2 ->
              Option.(
                opt >>= fun map ->
                match Term.pattern_match bvs t1 t2 with
                | Some theta ->
                    Some
                      (Map.force_merge theta
                         map
                         (*~catch_dup:(fun (tvar, t1, t2) ->
                           print_endline @@ sprintf "%s : %s != %s"
                             (Ident.name_of_tvar tvar) (Term.str_of t1) (Term.str_of t2))*))
                | None -> None))
        with _ -> (*nonlinear pattern not supported*) None)
    | _ -> None
end

and Formula :
  (Type.FormulaType
    with type term := Term.t
     and type atom := Atom.t
     and type rand := Rand.t
     and type predicate_fixpoint := Predicate.fixpoint
     and type termSubst := TermSubst.t
     and type predSubst := PredSubst.t
     and type funcSubst := FuncSubst.t) = struct
  type unop = Not
  type binop = And | Or | Imply | Iff | Xor
  type binder = Forall | Exists | Random of Rand.t

  type t =
    | Atom of Atom.t * info
    | UnaryOp of unop * Formula.t * info
    | BinaryOp of binop * Formula.t * Formula.t * info
    | Bind of binder * sort_env_list * Formula.t * info
    | LetRec of t def list * Formula.t * info
    | LetFormula of Ident.tvar * Sort.t * Term.t * Formula.t * info

  and 'a def = {
    kind : Predicate.fixpoint;
    name : Ident.pvar;
    args : sort_env_list;
    body : 'a;
  }

  (** Sorts *)

  let subst_sorts_bounds map =
    List.map ~f:(fun (x, s) -> (x, Term.subst_sorts_sort map s)) >> List.unique

  let subst_conts_bounds map =
    List.map ~f:(fun (x, s) -> (x, Term.subst_conts_sort map s)) >> List.unique

  let subst_opsigs_bounds map =
    List.map ~f:(fun (x, s) -> (x, Term.subst_opsigs_sort map s)) >> List.unique

  (** Binders *)

  let flip_quantifier = function
    | Forall -> Exists
    | Exists -> Forall
    | Random r -> Random r

  let str_of_binder = function
    | Forall -> "Forall"
    | Exists -> "Exists"
    | Random r -> Rand.str_of r

  let flip_binop = function
    | And -> Or
    | Or -> And
    | Iff -> Xor
    | Xor -> Iff
    | Imply -> failwith "Imply not supported"

  let str_of_unop = function Not -> "Not"

  let str_of_binop = function
    | And -> "And"
    | Or -> "Or"
    | Imply -> "Imply"
    | Iff -> "Iff"
    | Xor -> "Xor"

  (** Construction *)

  let mk_atom ?(info = Dummy) atom = Atom (atom, info)
  let mk_unop ?(info = Dummy) op phi = UnaryOp (op, phi, info)

  let rec mk_neg ?(info = Dummy) = function
    | LetFormula (var, sort, def, body, info) ->
        LetFormula (var, sort, def, mk_neg body, info)
    | phi -> UnaryOp (Not, phi, info)

  let mk_binop ?(info = Dummy) op phi1 phi2 = BinaryOp (op, phi1, phi2, info)
  let mk_and ?(info = Dummy) phi1 phi2 = BinaryOp (And, phi1, phi2, info)
  let mk_or ?(info = Dummy) phi1 phi2 = BinaryOp (Or, phi1, phi2, info)
  let mk_imply ?(info = Dummy) phi1 phi2 = BinaryOp (Imply, phi1, phi2, info)
  let mk_iff ?(info = Dummy) phi1 phi2 = BinaryOp (Iff, phi1, phi2, info)
  let mk_xor ?(info = Dummy) phi1 phi2 = BinaryOp (Xor, phi1, phi2, info)

  let mk_bind ?(info = Dummy) binder bound body =
    Bind (binder, bound, body, info)

  let rec mk_binds quantifiers f =
    match quantifiers with
    | [] -> f
    | (binder, sortenv) :: tl -> mk_bind binder sortenv (mk_binds tl f)

  let mk_bind_if_bounded ?(info = Dummy) binder bound body =
    if List.is_empty bound then body else mk_bind binder bound body ~info

  let mk_forall ?(info = Dummy) bound body = Bind (Forall, bound, body, info)
  let mk_exists ?(info = Dummy) bound body = Bind (Exists, bound, body, info)
  let mk_forall_if_bounded ?(info = Dummy) = mk_bind_if_bounded Forall ~info
  let mk_exists_if_bounded ?(info = Dummy) = mk_bind_if_bounded Exists ~info
  let mk_random ?(info = Dummy) r bound body = Bind (Random r, bound, body, info)

  let rec mk_randoms rands f =
    match rands with
    | [] -> f
    | (var, rand) :: tl ->
        mk_random rand [ (var, Rand.sort_of rand) ] (mk_randoms tl f)

  let mk_let_formula ?(info = Dummy) var sort def body =
    LetFormula (var, sort, def, body, info)

  let mk_letrec ?(info = Dummy) funcs body = LetRec (funcs, body, info)
  let mk_false ?(info = Dummy) () = Atom (Atom.mk_false (), info)
  let mk_true ?(info = Dummy) () = Atom (Atom.mk_true (), info)
  let mk_bool b = if b then mk_true () else mk_false ()

  let rec negate = function
    | Atom (atom, info) as phi -> (
        match Atom.negate atom with
        | None -> mk_neg phi
        | Some neg_atom -> Atom (neg_atom, info))
    | UnaryOp (Not, phi, _) -> phi
    | LetFormula (var, sort, def, body, info) ->
        LetFormula (var, sort, def, negate body, info)
    | phi -> mk_neg phi (*ToDo*)

  let of_bool_var b = mk_atom (Atom.of_bool_var b)
  let of_neg_bool_var b = mk_atom (Atom.of_neg_bool_var b)

  let rec of_bool_term = function
    | Term.FunApp (T_bool.Formula phi, _, _) -> phi
    | Term.FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
        let p1 = of_bool_term t1 in
        let p2 = of_bool_term t2 in
        let p3 = of_bool_term t3 in
        mk_or (mk_and p1 p2) (mk_and (negate p1) p3) ~info
    | Term.LetTerm (var, sort, def, body, info) ->
        LetFormula (var, sort, def, of_bool_term body, info)
    | t -> mk_atom @@ Atom.of_bool_term t

  let rec of_neg_bool_term = function
    | Term.FunApp (T_bool.Formula phi, _, _) -> negate phi
    | Term.FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
        let p1 = of_bool_term t1 in
        let p2 = of_neg_bool_term t2 in
        let p3 = of_neg_bool_term t3 in
        mk_or (mk_and p1 p2) (mk_and (negate p1) p3) ~info
    | Term.LetTerm (var, sort, def, body, info) ->
        LetFormula (var, sort, def, of_neg_bool_term body, info)
    | t -> mk_atom @@ Atom.of_neg_bool_term t

  let and_of phis =
    let rec aux acc = function
      | [] -> ( match acc with None -> mk_true () | Some phi -> phi)
      | Atom (Atom.True _, _) :: phis' -> aux acc phis'
      | Atom (Atom.False _, _) :: _ -> mk_false ()
      | phi :: phis' -> (
          match acc with
          | None -> aux (Some phi) phis'
          | Some phi' -> aux (Some (mk_and phi' phi)) phis')
    in
    aux None phis

  let or_of phis =
    let rec aux acc = function
      | [] -> ( match acc with None -> mk_false () | Some phi -> phi)
      | Atom (Atom.False _, _) :: phis' -> aux acc phis'
      | Atom (Atom.True _, _) :: _ -> mk_true ()
      | phi :: phis' -> (
          match acc with
          | None -> aux (Some phi) phis'
          | Some phi' -> aux (Some (mk_or phi' phi)) phis')
    in
    aux None phis

  let xor_of = function
    | [ Atom (Atom.True _, _); Atom (Atom.True _, _) ]
    | [ Atom (Atom.False _, _); Atom (Atom.False _, _) ] ->
        mk_false ()
    | [ Atom (Atom.True _, _); Atom (Atom.False _, _) ]
    | [ Atom (Atom.False _, _); Atom (Atom.True _, _) ] ->
        mk_true ()
    | [ Atom (Atom.True _, _); phi ] | [ phi; Atom (Atom.True _, _) ] ->
        mk_neg phi
    | [ Atom (Atom.False _, _); phi ] | [ phi; Atom (Atom.False _, _) ] -> phi
    | [ phi1; phi2 ] ->
        mk_or (mk_and (mk_neg phi1) phi2) (mk_and phi1 (mk_neg phi2))
    | _ -> assert false

  let geq t1 t2 =
    mk_atom
      ((if T_int.is_sint t1 && T_int.is_sint t2 then T_int.mk_geq
        else T_real.mk_rgeq)
         t1 t2)

  let gt t1 t2 =
    mk_atom
      ((if T_int.is_sint t1 && T_int.is_sint t2 then T_int.mk_gt
        else T_real.mk_rgt)
         t1 t2)

  let leq t1 t2 =
    mk_atom
      ((if T_int.is_sint t1 && T_int.is_sint t2 then T_int.mk_leq
        else T_real.mk_rleq)
         t1 t2)

  let lt t1 t2 =
    mk_atom
      ((if T_int.is_sint t1 && T_int.is_sint t2 then T_int.mk_lt
        else T_real.mk_rlt)
         t1 t2)

  let eq t1 t2 = mk_atom (T_bool.mk_eq t1 t2)
  let eqs ts = List.map ~f:mk_atom (T_bool.mk_eqs ts)
  let neq t1 t2 = mk_atom (T_bool.mk_neq t1 t2)

  let mk_range v lb ub =
    [ Formula.leq (T_int.mk_int lb) v; Formula.leq v (T_int.mk_int ub) ]

  let mk_range_opt v lb ub =
    match (lb, ub) with
    | None, None -> []
    | None, Some ub -> [ Formula.leq v (T_int.mk_int ub) ]
    | Some lb, None -> [ Formula.leq (T_int.mk_int lb) v ]
    | Some lb, Some ub ->
        [ Formula.leq (T_int.mk_int lb) v; Formula.leq v (T_int.mk_int ub) ]

  let mk_range_real v lb ub =
    [ Formula.leq (T_real.mk_real lb) v; Formula.leq v (T_real.mk_real ub) ]

  let mk_range_real_opt v lb ub =
    match (lb, ub) with
    | None, None -> []
    | None, Some ub -> [ Formula.leq v (T_real.mk_real ub) ]
    | Some lb, None -> [ Formula.leq (T_real.mk_real lb) v ]
    | Some lb, Some ub ->
        [ Formula.leq (T_real.mk_real lb) v; Formula.leq v (T_real.mk_real ub) ]

  (** Destruction *)

  let let_atom = function
    | Atom (atom, info) -> (atom, info)
    | _ -> assert false

  let let_eq = function
    | Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), info) ->
        (t1, t2, info)
    | _ -> assert false

  let let_unop = function
    | UnaryOp (op, phi, info) -> (op, phi, info)
    | _ -> assert false

  let let_neg = function
    | UnaryOp (Not, phi, info) -> (phi, info)
    | _ -> assert false

  let let_binop = function
    | BinaryOp (op, phi1, phi2, info) -> (op, phi1, phi2, info)
    | _ -> assert false

  let let_and = function
    | BinaryOp (And, phi1, phi2, info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_or = function
    | BinaryOp (Or, phi1, phi2, info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_imply = function
    | BinaryOp (Imply, phi1, phi2, info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_iff = function
    | BinaryOp (Iff, phi1, phi2, info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_xor = function
    | BinaryOp (Xor, phi1, phi2, info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_bind = function
    | Bind (binder, params, body, info) -> (binder, params, body, info)
    | _ -> assert false

  let let_forall = function
    | Bind (Forall, params, body, info) -> (params, body, info)
    | _ -> assert false

  let let_exists = function
    | Bind (Exists, params, body, info) -> (params, body, info)
    | _ -> assert false

  let let_forall_or_formula = function
    | Bind (Forall, params, body, info) -> (params, body, info)
    | fml -> ([], fml, Dummy)

  let let_exists_or_formula = function
    | Bind (Exists, params, body, info) -> (params, body, info)
    | fml -> ([], fml, Dummy)

  let let_letrec = function
    | LetRec (funcs, body, info) -> (funcs, body, info)
    | _ -> assert false

  let rec body_of_let = function
    | LetFormula (_, _, _, body, _) -> body_of_let body
    | phi -> phi

  (** Morphism *)

  let map_funcs ~f = List.map ~f:(fun def -> { def with body = f def.body })

  let rec fold ~f = function
    | Atom (atom, _) -> f#fatom atom
    | UnaryOp (Not, phi, _) -> f#fnot (fold ~f phi)
    | BinaryOp (And, phi1, phi2, _) -> f#fand (fold ~f phi1) (fold ~f phi2)
    | BinaryOp (Or, phi1, phi2, _) -> f#for_ (fold ~f phi1) (fold ~f phi2)
    | BinaryOp (Imply, phi1, phi2, _) -> f#fimply (fold ~f phi1) (fold ~f phi2)
    | BinaryOp (Iff, phi1, phi2, _) -> f#fiff (fold ~f phi1) (fold ~f phi2)
    | BinaryOp (Xor, phi1, phi2, _) -> f#fxor (fold ~f phi1) (fold ~f phi2)
    | Bind (binder, senv, phi, _) -> f#fbind binder senv (fold ~f phi)
    | LetRec (funcs, phi, _) ->
        f#fletrec (map_funcs ~f:(fold ~f) funcs) (fold ~f phi)
    | LetFormula (tvar, sort, def, body, _) ->
        f#flet tvar sort def (fold ~f body)

  let map_term ~f =
    fold
      ~f:
        (object
           method fatom atom = Formula.mk_atom @@ Atom.map_term ~f atom
           method fnot p1 = mk_neg p1
           method fand p1 p2 = mk_and p1 p2
           method for_ p1 p2 = mk_or p1 p2
           method fimply p1 p2 = mk_imply p1 p2
           method fiff p1 p2 = mk_iff p1 p2
           method fxor p1 p2 = mk_xor p1 p2
           method fbind binder senv p1 = mk_bind binder senv p1
           method fletrec funcs p1 = mk_letrec funcs p1

           method flet tvar sort def body =
             mk_let_formula tvar sort (Term.map_term true ~f def) body
        end)

  let iter_term ~f t =
    let _ =
      map_term t ~f:(fun t ->
          f t;
          t)
    in
    ()

  let map_atom ~f =
    fold
      ~f:
        (object
           method fatom atom = f atom
           method fnot p1 = mk_neg p1
           method fand p1 p2 = mk_and p1 p2
           method for_ p1 p2 = mk_or p1 p2
           method fimply p1 p2 = mk_imply p1 p2
           method fiff p1 p2 = mk_iff p1 p2
           method fxor p1 p2 = mk_xor p1 p2
           method fbind binder senv p1 = mk_bind binder senv p1
           method fletrec funcs p1 = mk_letrec funcs p1

           method flet tvar sort def body =
             mk_let_formula tvar sort (Term.map_atom ~f def) body
        end)

  let map_atom_polarity ~f =
    fold
      ~f:
        (object
           method fatom atom polarity = f polarity atom
           method fnot p1 polarity = mk_neg (p1 @@ not polarity)
           method fand p1 p2 polarity = mk_and (p1 polarity) (p2 polarity)
           method for_ p1 p2 polarity = mk_or (p1 polarity) (p2 polarity)

           method fimply p1 p2 polarity =
             mk_imply (p1 @@ not polarity) (p2 polarity)

           method fiff _p1 _p2 _polarity = failwith "not supported"
           method fxor _p1 _p2 _polarity = failwith "not supported"

           method fbind binder senv p1 polarity =
             mk_bind binder senv (p1 polarity)

           method fletrec funcs p1 polarity =
             mk_letrec (map_funcs funcs ~f:(fun f -> f polarity)) (p1 polarity)

           method flet tvar sort def body polarity =
             mk_let_formula tvar sort
               (Term.map_atom_polarity ~f def polarity)
               (body polarity)
        end)

  let iter_atom ~f phi =
    ignore
    @@ map_atom phi ~f:(fun atm ->
           f atm;
           Formula.mk_atom atm);
    ()

  (** Printing *)

  let str_of ?(priority = Priority.lowest) =
    let rec aux ?(priority = Priority.lowest) ~next = function
      | Atom (atom, _) -> next @@ Atom.str_of ~priority atom
      | UnaryOp (Not, phi, _) ->
          aux ~priority:(Priority.fun_app + 1 (*ToDo*)) phi ~next:(fun s ->
              next
              @@ Priority.add_paren priority Priority.fun_app
              @@ sprintf "not %s" s)
      | BinaryOp (And, phi1, phi2, _) ->
          aux ~priority:Priority.binary_and phi1 ~next:(fun s1 ->
              aux ~priority:Priority.binary_and phi2 ~next:(fun s2 ->
                  next
                  @@ Priority.add_paren priority Priority.binary_and
                  @@ sprintf "%s /\\ %s" s1 s2))
      | BinaryOp (Or, phi1, phi2, _) ->
          aux ~priority:Priority.binary_or phi1 ~next:(fun s1 ->
              aux ~priority:Priority.binary_or phi2 ~next:(fun s2 ->
                  next
                  @@ Priority.add_paren priority Priority.binary_or
                  @@ sprintf "%s \\/ %s" s1 s2))
      | BinaryOp (Imply, phi1, phi2, _) ->
          aux phi1 ~priority:Priority.imply_iff_xor ~next:(fun s1 ->
              aux phi2 ~priority:Priority.imply_iff_xor ~next:(fun s2 ->
                  next
                  @@ Priority.add_paren priority Priority.imply_iff_xor
                  @@ sprintf "%s => %s" s1 s2))
      | BinaryOp (Iff, phi1, phi2, _) ->
          aux phi1 ~priority:Priority.imply_iff_xor ~next:(fun s1 ->
              aux phi2 ~priority:Priority.imply_iff_xor ~next:(fun s2 ->
                  next
                  @@ Priority.add_paren priority Priority.imply_iff_xor
                  @@ sprintf "%s <=> %s" s1 s2))
      | BinaryOp (Xor, phi1, phi2, _) ->
          aux phi1 ~priority:Priority.imply_iff_xor ~next:(fun s1 ->
              aux phi2 ~priority:Priority.imply_iff_xor ~next:(fun s2 ->
                  next
                  @@ Priority.add_paren priority Priority.imply_iff_xor
                  @@ sprintf "%s xor %s" s1 s2))
      | Bind (Forall, params, phi, _) ->
          aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
              next
              @@ Priority.add_paren priority Priority.let_forall_exists
              @@ sprintf "forall %s. %s"
                   (str_of_sort_env_list Term.str_of_sort params)
                   s)
      | Bind (Exists, params, phi, _) ->
          aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
              next
              @@ Priority.add_paren priority Priority.let_forall_exists
              @@ sprintf "exists %s. %s"
                   (str_of_sort_env_list Term.str_of_sort params)
                   s)
      | Bind (Random r, params, phi, _) ->
          aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
              next
              @@ Priority.add_paren priority Priority.let_forall_exists
              @@ sprintf "%s %s. %s" (Rand.str_of r)
                   (str_of_sort_env_list Term.str_of_sort params)
                   s)
      | LetRec (funcs, body, _) ->
          aux body ~priority:Priority.let_forall_exists ~next:(fun s ->
              next
              @@ Priority.add_paren priority Priority.let_forall_exists
              @@ sprintf "let rec %s in %s"
                   (String.concat_map_list ~sep:" and " funcs ~f:(fun def ->
                        let var_names =
                          if List.is_empty def.args then [ "()" ]
                          else List.map def.args ~f:(fst >> Ident.name_of_tvar)
                        in
                        aux def.body ~priority:Priority.lowest ~next:(fun s ->
                            sprintf "%s %s =%s %s"
                              (Ident.name_of_pvar def.name)
                              (String.concat ~sep:" " var_names)
                              (Predicate.str_of_fop def.kind)
                              s)))
                   s)
      | LetFormula (var, sort, def, phi, _) ->
          aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
              next
              @@ Priority.add_paren priority Priority.let_forall_exists
              @@ sprintf "letf %s:%s = %s in %s" (Ident.name_of_tvar var)
                   (Term.short_name_of_sort sort)
                   (Term.str_of def) s)
    in
    aux ~priority ~next:Fn.id

  (** Observation *)

  let is_atom = function Atom (_, _) -> true | _ -> false
  let is_true = function Atom (Atom.True _, _) -> true | _ -> false
  let is_false = function Atom (Atom.False _, _) -> true | _ -> false

  let is_eq = function
    | Atom (Atom.App (Predicate.Psym T_bool.Eq, [ _t1; _t2 ], _), _) -> true
    | _ -> false

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

  let is_let_free =
    fold
      ~f:
        (object
           method fatom atom = Atom.is_let_free atom
           method fnot r1 = r1
           method fand r1 r2 = r1 && r2
           method for_ r1 r2 = r1 && r2
           method fimply r1 r2 = r1 && r2
           method fiff r1 r2 = r1 && r2
           method fxor r1 r2 = r1 && r2
           method fbind _ _senv r1 = r1
           method fletrec _funcs _r1 = false
           method flet _tvar _sort _def _body = false
        end)

  let is_quantifier_free =
    fold
      ~f:
        (object
           method fatom atom = Atom.is_quantifier_free atom
           method fnot r1 = r1
           method fand r1 r2 = r1 && r2
           method for_ r1 r2 = r1 && r2
           method fimply r1 r2 = r1 && r2
           method fiff r1 r2 = r1 && r2
           method fxor r1 r2 = r1 && r2
           method fbind _ _senv _r1 = false

           method fletrec funcs r1 =
             List.for_all funcs ~f:(fun def -> def.body) && r1

           method flet _tvar _sort def r1 = Term.is_quantifier_free def && r1
        end)

  let tvs_of =
    fold
      ~f:
        (object
           method fatom atom = Atom.tvs_of atom
           method fnot r1 = r1
           method fand r1 r2 = Set.union r1 r2
           method for_ r1 r2 = Set.union r1 r2
           method fimply r1 r2 = Set.union r1 r2
           method fiff r1 r2 = Set.union r1 r2
           method fxor r1 r2 = Set.union r1 r2

           method fbind _ senv r1 =
             Set.diff r1 (Set.Poly.of_list @@ List.map ~f:fst senv)

           method fletrec funcs r1 =
             Set.diff
               (Set.Poly.union_list
               @@ r1
                  :: List.map funcs ~f:(fun def ->
                         Set.diff def.body
                           (Set.Poly.of_list @@ List.map ~f:fst def.args)))
               (Set.Poly.of_list
               @@ List.map funcs ~f:(fun def -> Ident.pvar_to_tvar def.name))

           method flet x _ def r1 =
             Set.union (Term.tvs_of def) (Set.remove r1 x)
        end)

  let pvs_of =
    fold
      ~f:
        (object
           method fatom atom = Atom.pvs_of atom
           method fnot r1 = r1
           method fand r1 r2 = Set.union r1 r2
           method for_ r1 r2 = Set.union r1 r2
           method fimply r1 r2 = Set.union r1 r2
           method fiff r1 r2 = Set.union r1 r2
           method fxor r1 r2 = Set.union r1 r2
           method fbind _ _ r1 = r1

           method fletrec funcs r1 =
             Set.diff
               (Set.Poly.union_list
               @@ r1
                  :: List.map funcs ~f:(fun def ->
                         Set.diff def.body
                           (Set.Poly.map ~f:Ident.tvar_to_pvar
                           @@ Set.Poly.of_list @@ List.map ~f:fst def.args)))
               (Set.Poly.of_list @@ List.map funcs ~f:(fun def -> def.name))

           method flet x _ def r1 =
             Set.union (Term.pvs_of def) (Set.remove r1 (Ident.tvar_to_pvar x))
        end)

  let fvs_of phi =
    Set.union (tvs_of phi)
    @@ Set.Poly.map ~f:Ident.pvar_to_tvar
    (*ToDo*) @@ pvs_of phi

  let svs_of =
    fold
      ~f:
        (object
           method fatom atom = Atom.svs_of atom
           method fnot r1 = r1
           method fand r1 r2 = Set.union r1 r2
           method for_ r1 r2 = Set.union r1 r2
           method fimply r1 r2 = Set.union r1 r2
           method fiff r1 r2 = Set.union r1 r2
           method fxor r1 r2 = Set.union r1 r2

           method fbind _ senv r1 =
             Set.union
               (Set.Poly.of_list
               @@ List.filter_map ~f:(function
                    | Sort.SVar svar -> Some svar
                    | _ -> None)
               @@ List.map ~f:snd senv)
               r1

           method fletrec funcs r1 =
             Set.Poly.union_list
             @@ r1
                :: List.map funcs ~f:(fun def ->
                       Set.union
                         (Set.Poly.of_list
                         @@ List.filter_map ~f:(function
                              | Sort.SVar svar -> Some svar
                              | _ -> None)
                         @@ List.map ~f:snd def.args)
                         def.body)

           method flet _ sort def r1 =
             Set.Poly.union_list
               [
                 Term.svs_of def;
                 r1;
                 (match sort with
                 | Sort.SVar svar -> Set.Poly.singleton svar
                 | _ -> Set.Poly.empty);
               ]
        end)

  let term_sort_env_of ?(bvs = Set.Poly.empty) phi =
    fold
      ~f:
        (object
           method fatom atom bvs = Atom.term_sort_env_of ~bvs atom
           method fnot r1 bvs = r1 bvs
           method fand r1 r2 bvs = Set.union (r1 bvs) (r2 bvs)
           method for_ r1 r2 bvs = Set.union (r1 bvs) (r2 bvs)
           method fimply r1 r2 bvs = Set.union (r1 bvs) (r2 bvs)
           method fiff r1 r2 bvs = Set.union (r1 bvs) (r2 bvs)
           method fxor r1 r2 bvs = Set.union (r1 bvs) (r2 bvs)

           method fbind _ senv r1 bvs =
             Set.diff (r1 bvs) (Set.Poly.of_list senv)

           method fletrec funcs r1 bvs =
             Set.Poly.union_list
             @@ r1 bvs
                :: List.map funcs ~f:(fun def ->
                       Set.diff (def.body bvs) (Set.Poly.of_list def.args))

           method flet tvar sort def body bvs =
             Set.remove
               (Set.union
                  (Term.term_sort_env_of ~bvs def)
                  (body (Set.add bvs tvar)))
               (tvar, sort)
        end)
      phi bvs

  let pred_sort_env_of ?(bpvs = Set.Poly.empty) phi =
    fold
      ~f:
        (object
           method fatom atom bpvs = Atom.pred_sort_env_of ~bpvs atom
           method fnot r1 bpvs = r1 bpvs
           method fand r1 r2 bpvs = Set.union (r1 bpvs) (r2 bpvs)
           method for_ r1 r2 bpvs = Set.union (r1 bpvs) (r2 bpvs)
           method fimply r1 r2 bpvs = Set.union (r1 bpvs) (r2 bpvs)
           method fiff r1 r2 bpvs = Set.union (r1 bpvs) (r2 bpvs)
           method fxor r1 r2 bpvs = Set.union (r1 bpvs) (r2 bpvs)
           method fbind _ _ r1 bpvs = r1 bpvs

           method fletrec funcs r1 bpvs =
             let bpvs =
               Set.union bpvs @@ Set.Poly.of_list
               @@ List.map funcs ~f:(fun def -> def.name)
             in
             Set.Poly.union_list
               (r1 bpvs :: List.map funcs ~f:(fun def -> def.body bpvs))

           method flet _ _ def body bpvs =
             Set.union (Term.pred_sort_env_of ~bpvs def) (body bpvs)
        end)
      phi bpvs

  let sort_env_of ?(bpvs = Set.Poly.empty) phi =
    Set.union (term_sort_env_of phi)
      (Term.pred_to_sort_env @@ pred_sort_env_of ~bpvs phi)

  let rec conjuncts_of = function
    | BinaryOp (And, phi1, phi2, _) ->
        Set.union (conjuncts_of phi1) (conjuncts_of phi2)
    | phi -> Set.Poly.singleton phi

  let rec conjuncts_list_of = function
    | BinaryOp (And, phi1, phi2, _) ->
        conjuncts_list_of phi1 @ conjuncts_list_of phi2
    | phi -> [ phi ]

  let rec disjuncts_of = function
    | BinaryOp (Or, phi1, phi2, _) ->
        Set.union (disjuncts_of phi1) (disjuncts_of phi2)
    | phi -> Set.Poly.singleton phi

  let rec disjuncts_list_of = function
    | BinaryOp (Or, phi1, phi2, _) ->
        disjuncts_list_of phi1 @ disjuncts_list_of phi2
    | phi -> [ phi ]

  let funsyms_of =
    fold
      ~f:
        (object
           method fatom atom = Atom.funsyms_of atom
           method fnot r1 = r1
           method fand r1 r2 = Set.union r1 r2
           method for_ r1 r2 = Set.union r1 r2
           method fimply r1 r2 = Set.union r1 r2
           method fiff r1 r2 = Set.union r1 r2
           method fxor r1 r2 = Set.union r1 r2
           method fbind _ _ r1 = r1
           method fletrec _funcs _r1 = failwith "not implemented"
           method flet _ _ def r1 = Set.union (Term.funsyms_of def) r1
        end)

  let predsyms_of =
    fold
      ~f:
        (object
           method fatom atom = Atom.predsyms_of atom
           method fnot r1 = r1
           method fand r1 r2 = Set.union r1 r2
           method for_ r1 r2 = Set.union r1 r2
           method fimply r1 r2 = Set.union r1 r2
           method fiff r1 r2 = Set.union r1 r2
           method fxor r1 r2 = Set.union r1 r2
           method fbind _ _ r1 = r1
           method fletrec _funcs _r1 = failwith "not implemented"
           method flet _ _ def r1 = Set.union (Term.predsyms_of def) r1
        end)

  let rec pathexps_of ?(bvs = Set.Poly.empty) = function
    | Atom (atom, _) -> Atom.pathexps_of ~bvs atom
    | UnaryOp (_, phi, _) -> pathexps_of ~bvs phi
    | BinaryOp (_, phi1, phi2, _) ->
        Set.union (pathexps_of ~bvs phi1) (pathexps_of ~bvs phi2)
    | Bind (_, senv, phi, _) ->
        let bvs = Set.union bvs (Set.Poly.of_list @@ List.map ~f:fst senv) in
        pathexps_of ~bvs phi
    | LetRec (funcs, phi, _) ->
        Set.Poly.union_list
        @@ pathexps_of ~bvs phi
           :: List.map funcs ~f:(fun def ->
                  let bvs =
                    Set.union bvs (Set.Poly.of_list @@ List.map ~f:fst def.args)
                  in
                  pathexps_of ~bvs def.body)
    | LetFormula (var, _, def, body, _) ->
        Set.union
          (Term.pathexps_of ~bvs def)
          (pathexps_of ~bvs:(Set.add bvs var) body)

  let rec terms_of = function
    | Atom (atom, _) -> Atom.terms_of atom
    | UnaryOp (_, phi, _) -> terms_of phi
    | BinaryOp (_, p1, p2, _) -> Set.union (terms_of p1) (terms_of p2)
    | _ -> failwith "not implemented yet"

  let rec fvar_apps_of = function
    | Atom (atom, _) -> Atom.fvar_apps_of atom
    | UnaryOp (_, phi, _) -> fvar_apps_of phi
    | BinaryOp (_, p1, p2, _) -> Set.union (fvar_apps_of p1) (fvar_apps_of p2)
    | _ -> failwith "not implemented yet"

  let rec filtered_terms_of ~f = function
    | Atom (atom, _) -> Atom.filtered_terms_of ~f atom
    | UnaryOp (_, phi, _) -> filtered_terms_of ~f phi
    | BinaryOp (_, phi1, phi2, _) ->
        Set.union (filtered_terms_of ~f phi1) (filtered_terms_of ~f phi2)
    | Bind (_, senv, phi, _) ->
        Set.diff (filtered_terms_of ~f phi)
          (Set.Poly.of_list @@ Term.of_sort_env senv)
    | LetRec (funcs, phi, _) ->
        Set.Poly.union_list
        @@ filtered_terms_of ~f phi
           :: List.map funcs ~f:(fun def ->
                  Set.diff
                    (filtered_terms_of ~f def.body)
                    (Set.Poly.of_list @@ Term.of_sort_env def.args))
    | LetFormula (var, sort, def, body, info) ->
        Term.filtered_terms_of ~f
        @@ LetTerm (var, sort, def, T_bool.of_formula body, info)

  (* assume that the argument is let-normalized *)
  (* assume that [phi] is let-normalized *)
  let rec atoms_of ?(nrec = false) ?(pos = true) = function
    | UnaryOp (Not, phi, _) -> atoms_of ~nrec ~pos:(not pos) phi
    (*| UnaryOp (_, phi, _) -> aux pos phi*)
    | BinaryOp (Imply, phi1, phi2, _) ->
        let pos1, neg1 = atoms_of ~nrec ~pos:(not pos) phi1 in
        let pos2, neg2 = atoms_of ~nrec ~pos phi2 in
        (Set.union pos1 pos2, Set.union neg1 neg2)
    | BinaryOp ((Iff | Xor), _, _, _) -> assert false
    | BinaryOp ((And | Or), phi1, phi2, _) ->
        let pos1, neg1 = atoms_of ~nrec ~pos phi1 in
        let pos2, neg2 = atoms_of ~nrec ~pos phi2 in
        (Set.union pos1 pos2, Set.union neg1 neg2)
    | Atom (atom, _) ->
        if nrec then
          if pos then (Set.Poly.singleton atom, Set.Poly.empty)
          else (Set.Poly.empty, Set.Poly.singleton atom)
        else Atom.atoms_of ~pos atom
    | Bind (_, _, phi, _) -> atoms_of ~nrec ~pos phi
    | LetRec (_funcs, _body, _) -> assert false
    (*Set.Poly.union_list @@
      aux pos body :: List.map funcs ~f:(Quadruple.fth >> aux pos)*)
    | LetFormula (_, _, def, body, _) ->
        let pos1, neg1 = Term.atoms_of ~pos def in
        let pos2, neg2 = atoms_of ~nrec ~pos body in
        (Set.union pos1 pos2, Set.union neg1 neg2)

  (* assume that the argument is alpha-renamed *)
  let rec let_env_of ?(map = Map.Poly.empty) = function
    | LetFormula (var, _, def, body, _) ->
        let_env_of
          ~map:(Map.Poly.set map ~key:var ~data:(Term.subst map def))
          body
    | UnaryOp (_, phi, _) -> let_env_of phi ~map
    | BinaryOp (_, phi1, phi2, _) -> let_env_of phi2 ~map:(let_env_of phi1 ~map)
    | Bind (_, _, phi, _) -> let_env_of phi ~map
    | Atom (atom, _) -> Atom.let_env_of atom ~map
    | LetRec _ -> map

  (* assume that the argument is alpha-renamed *)
  let rec let_sort_env_of ?(map = Map.Poly.empty) = function
    | LetFormula (var, sort, _, body, _) ->
        let_sort_env_of ~map:(Map.Poly.set map ~key:var ~data:sort) body
    | UnaryOp (_, phi, _) -> let_sort_env_of phi ~map
    | BinaryOp (_, phi1, phi2, _) ->
        let_sort_env_of phi2 ~map:(let_sort_env_of phi1 ~map)
    | Bind (_, _, phi, _) -> let_sort_env_of phi ~map
    | Atom (atom, _) -> Atom.let_sort_env_of atom ~map
    | LetRec _ -> map

  let nesting_level =
    fold
      ~f:
        (object
           method fatom atom = Atom.nesting_level atom
           method fnot r1 = r1
           method fand r1 r2 = max r1 r2
           method for_ r1 r2 = max r1 r2
           method fimply r1 r2 = max r1 r2
           method fiff r1 r2 = max r1 r2
           method fxor r1 r2 = max r1 r2
           method fbind _ _ r1 = r1

           method fletrec funcs r1 =
             Integer.max_list (r1 :: List.map funcs ~f:(fun def -> 1 + def.body))

           method flet _ _ _def _body =
             failwith "[nesting_level] 'LetFormula' not supported"
        end)

  let number_of_quantifiers =
    fold
      ~f:
        (object
           method fatom atom = Atom.number_of_quantifiers atom
           method fnot r1 = r1
           method fand r1 r2 = r1 + r2
           method for_ r1 r2 = r1 + r2
           method fimply r1 r2 = r1 + r2
           method fiff r1 r2 = r1 + r2
           method fxor r1 r2 = r1 + r2
           method fbind _ _ r1 = 1 + r1

           method fletrec funcs r1 =
             Integer.sum_list (r1 :: List.map funcs ~f:(fun def -> def.body))

           method flet _ _ def body = body + Term.number_of_quantifiers def
        end)

  let rec number_of_pvar_apps ?(ex = Map.Poly.empty) is_pos = function
    | Atom (atom, _) -> Atom.number_of_pvar_apps ~ex is_pos atom
    | UnaryOp (Not, phi, _) -> number_of_pvar_apps ~ex (not is_pos) phi
    | BinaryOp (Imply, phi1, phi2, _) ->
        number_of_pvar_apps ~ex (not is_pos) phi1
        + number_of_pvar_apps ~ex is_pos phi2
    | BinaryOp ((Iff | Xor), _, _, _) -> assert false
    | BinaryOp ((And | Or), phi1, phi2, _) ->
        number_of_pvar_apps ~ex is_pos phi1
        + number_of_pvar_apps ~ex is_pos phi2
    | Bind (_, _, phi, _) -> number_of_pvar_apps ~ex is_pos phi
    | LetRec (_, _, _) -> assert false
    | LetFormula (var, sort, def, body, info) ->
        Term.number_of_pvar_apps ~ex is_pos
        @@ Term.LetTerm (var, sort, def, T_bool.of_formula body, info)

  (*List.fold (fun acc (_, _, _, phi) -> acc + number_of_pvar_apps ~ex is_pos phi)
    (number_of_pvar_apps ~ex is_pos body) def*)
  let rec count_pvar_apps = function
    | Atom (atom, _) -> Atom.count_pvar_apps atom
    | UnaryOp (Not, phi, _) ->
        List.Assoc.map (count_pvar_apps phi) ~f:(fun (pc, nc) -> (nc, pc))
    | BinaryOp (Imply, phi1, phi2, _) ->
        let r1 =
          List.Assoc.map (count_pvar_apps phi1) ~f:(fun (pc, nc) -> (nc, pc))
        in
        let r2 = count_pvar_apps phi2 in
        r1 @ r2
        |> List.group ~break:(fun x y -> Stdlib.(fst x <> fst y))
        (* |> Util.List.classify (fun x y -> fst x = fst y) *)
        |> List.map ~f:(function
             | [] -> assert false
             | x :: xs ->
                 ( fst x,
                   let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
                   (Integer.sum_list pcs, Integer.sum_list ncs) ))
    | BinaryOp ((Iff | Xor), _, _, _) -> assert false
    | BinaryOp ((And | Or), phi1, phi2, _) ->
        let r1 = count_pvar_apps phi1 in
        let r2 = count_pvar_apps phi2 in
        r1 @ r2
        |> List.group ~break:(fun x y -> Stdlib.(fst x <> fst y))
        (* |> Util.List.classify (fun x y -> fst x = fst y) *)
        |> List.map ~f:(function
             | [] -> assert false
             | x :: xs ->
                 ( fst x,
                   let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
                   (Integer.sum_list pcs, Integer.sum_list ncs) ))
    | Bind (_, _, phi, _) -> count_pvar_apps phi
    | LetRec (_, _, _) -> assert false
    | LetFormula _ ->
        failwith "[count_pvar_apps] 'LetFormula' not supported yet"

  let rec ast_size = function
    | Atom (atom, _) -> Atom.ast_size atom
    | UnaryOp (_, phi, _) -> 1 + ast_size phi
    | BinaryOp (_, phi1, phi2, _) -> 1 + ast_size phi1 + ast_size phi2
    | Bind (_, _, phi, _) -> 1 + ast_size phi
    | LetRec (funcs, phi, _) ->
        1
        + Integer.sum_list
            (ast_size phi :: List.map funcs ~f:(fun def -> ast_size def.body))
    | LetFormula (var, sort, def, body, info) ->
        Term.ast_size @@ LetTerm (var, sort, def, T_bool.of_formula body, info)
  (* let ast_size =
     Formula.fold
       ~f:
         (object
            method fatom atom = Atom.ast_size atom
            method fnot r1 = 1 + r1
            method fand r1 r2 = 1 + r1 + r2
            method for_ r1 r2 = 1 + r1 + r2
            method fimply r1 r2 = 1 + r1 + r2
            method fiff r1 r2 = 1 + r1 + r2
            method fxor r1 r2 = 1 + r1 + r2
            method fbind _ _ r1 = 1 + r1

            method fletrec funcs r1 =
              1 + Integer.sum_list (r1 :: List.map funcs ~f:(fun def -> def.body))

            method flet _ _ def body = 1 + Term.ast_size def + body
         end) *)

  let rec occur_times ?(map = Map.Poly.empty) x = function
    | Atom (atom, _) -> Atom.occur_times ~map x atom
    | BinaryOp (_, phi1, phi2, _) ->
        occur_times ~map x phi1 + occur_times ~map x phi2
    | UnaryOp (_, phi1, _) -> occur_times ~map x phi1
    | Bind (_, _, phi1, _) -> occur_times ~map x phi1
    | LetRec _ -> failwith "[occur_times_in_formula]unsupported letrec"
    | LetFormula (var, _, def, body, _) ->
        let map =
          Map.Poly.add_exn ~key:var ~data:(Term.occur_times ~map x def) map
        in
        occur_times ~map x body

  let div_rem_of =
    fold
      ~f:
        (object
           method fatom atom = Atom.div_rem_of atom
           method fnot r1 = r1
           method fand r1 r2 = Set.union r1 r2
           method for_ r1 r2 = Set.union r1 r2
           method fimply r1 r2 = Set.union r1 r2
           method fiff r1 r2 = Set.union r1 r2
           method fxor r1 r2 = Set.union r1 r2
           method fbind _ _ r1 = r1
           method fletrec _funcs _r1 = failwith "not implemented"
           method flet _ _ def r1 = Set.union (Term.div_rem_of def) r1
        end)

  (** Construction *)

  let bind ?(info = Dummy) binder bounds body =
    let ftv = fvs_of body in
    let bounds = List.filter ~f:(fst >> Set.mem ftv) bounds in
    mk_bind_if_bounded binder bounds body ~info

  let forall ?(info = Dummy) bounds body = bind ~info Forall bounds body
  let exists ?(info = Dummy) bounds body = bind ~info Exists bounds body

  let bind_fvs binder phi =
    mk_bind_if_bounded binder (Set.to_list @@ sort_env_of phi) phi ~info:Dummy

  let bind_fvs_with_exists = bind_fvs Exists
  let bind_fvs_with_forall = bind_fvs Forall

  let quantify_except ?(exists = true) args phi =
    let senv =
      Set.to_list
      @@ Set.filter ~f:(fst >> Set.mem args >> not)
      @@ Formula.term_sort_env_of phi
    in
    ( List.length senv,
      (if exists then Formula.exists else Formula.forall) senv phi )

  (** Substitution *)

  let rec rename map = function
    | Atom (atom, info) -> Atom (Atom.rename map atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, rename map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, rename map phi1, rename map phi2, info)
    | Bind (binder, bounds, body, info) -> (
        let map = Map.remove_keys map (List.map ~f:fst bounds) in
        match binder with
        | Random rand ->
            Bind (Random (Rand.rename map rand), bounds, rename map body, info)
        | _ -> Bind (binder, bounds, rename map body, info))
    | LetRec (funcs, body, info) ->
        let funcs =
          List.map funcs ~f:(fun def ->
              let map' = Map.remove_keys map (List.map ~f:fst def.args) in
              { def with body = rename map' def.body })
        in
        LetRec (funcs, rename map body, info)
    | LetFormula (var, sort, def, body, info) ->
        of_bool_term @@ Term.rename map
        @@ LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec rename_pvars map = function
    | Atom (atom, info) -> Atom (Atom.rename_pvars map atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, rename_pvars map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, rename_pvars map phi1, rename_pvars map phi2, info)
    | Bind (binder, bounds, body, info) ->
        Bind (binder, bounds, rename_pvars map body, info)
    | LetRec (funcs, body, info) ->
        let map' =
          Map.remove_keys map (List.map funcs ~f:(fun def -> def.name))
        in
        LetRec
          (map_funcs funcs ~f:(rename_pvars map'), rename_pvars map body, info)
    | LetFormula (var, sort, def, body, info) ->
        of_bool_term @@ Term.rename_pvars map
        @@ LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec rename_sorted_pvars map = function
    | Atom (atom, info) -> Atom (Atom.rename_sorted_pvars map atom, info)
    | UnaryOp (Not, phi, info) ->
        UnaryOp (Not, rename_sorted_pvars map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp
          (op, rename_sorted_pvars map phi1, rename_sorted_pvars map phi2, info)
    | Bind (binder, bounds, body, info) ->
        Bind (binder, bounds, rename_sorted_pvars map body, info)
    | LetRec (funcs, body, info) ->
        let map' =
          Map.remove_keys map
            (List.map funcs ~f:(fun def ->
                 (Ident.name_of_pvar def.name, List.map ~f:snd def.args)))
        in
        LetRec
          ( map_funcs funcs ~f:(rename_sorted_pvars map'),
            rename_sorted_pvars map body,
            info )
    | LetFormula (var, sort, def, body, info) ->
        of_bool_term
        @@ Term.rename_sorted_pvars map
        @@ LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec alpha_rename_let ?(map = Map.Poly.empty) = function
    | Atom (atom, info) -> Atom (Atom.alpha_rename_let ~map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, alpha_rename_let ~map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp
          (op, alpha_rename_let ~map phi1, alpha_rename_let ~map phi2, info)
    | Bind (binder, senv, body, info) ->
        let bounds = Set.Poly.of_list @@ List.map ~f:fst senv in
        let map' = Map.Poly.filter_keys map ~f:(Fn.non @@ Set.mem bounds) in
        Bind (binder, senv, alpha_rename_let ~map:map' body, info)
    | LetFormula (var, sort, def, body, info) ->
        let var' = Ident.mk_fresh_tvar () in
        let map' = Map.Poly.set ~key:var ~data:var' map in
        LetFormula
          ( var',
            sort,
            Term.alpha_rename_let ~map def,
            alpha_rename_let ~map:map' body,
            info )
    | LetRec _ as phi -> phi

  let refresh_tvar (senv, phi) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ()) in
    (Map.rename_keys_map map senv, rename map phi)

  let refresh_except args phi =
    Formula.refresh_tvar
      ( Map.of_set_exn
        @@ Set.filter ~f:(fst >> Set.mem args >> not)
        @@ Formula.term_sort_env_of phi,
        phi )

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
    let rec aux ~next map = function
      | Atom (Atom.App (Var (pvar, []), [], _), _)
        when Map.Poly.mem map @@ Ident.pvar_to_tvar pvar (*ToDo*) -> (
          match Map.Poly.find map (Ident.pvar_to_tvar pvar (*ToDo*)) with
          | Some t ->
              next @@ of_bool_term
              @@ if Term.is_var t then t else Term.subst map t
          | None -> next phi)
      | Atom (atom, info) -> next @@ Atom (Atom.subst map atom, info)
      | UnaryOp (Not, phi, info) ->
          aux map phi ~next:(fun phi' -> next @@ UnaryOp (Not, phi', info))
      | BinaryOp (op, phi1, phi2, info) ->
          aux map phi1 ~next:(fun phi1' ->
              aux map phi2 ~next:(fun phi2' ->
                  next @@ BinaryOp (op, phi1', phi2', info)))
      | Bind (binder, bounds, body, info) ->
          let map' = Map.remove_keys map (List.map ~f:fst bounds) in
          aux map' body ~next:(fun body' ->
              next @@ Bind (binder, bounds, body', info))
      | LetRec (funcs, body, info) ->
          let funcs =
            List.map funcs ~f:(fun def ->
                let map' = Map.remove_keys map (List.map ~f:fst def.args) in
                { def with body = subst map' def.body })
          in
          aux map body ~next:(fun body' -> next @@ LetRec (funcs, body', info))
      | LetFormula (var, sort, def, body, info) ->
          assert (not @@ Map.Poly.mem map var);
          aux map body ~next:(fun body' ->
              next @@ LetFormula (var, sort, Term.subst map def, body', info))
    in
    aux map phi ~next:Fn.id

  let subst_preds psub phi =
    fold
      ~f:
        (object
           method fatom atom psub = Atom.subst_preds psub atom
           method fnot phi1 psub = mk_neg (phi1 psub)
           method fand phi1 phi2 psub = mk_and (phi1 psub) (phi2 psub)
           method for_ phi1 phi2 psub = mk_or (phi1 psub) (phi2 psub)
           method fimply phi1 phi2 psub = mk_imply (phi1 psub) (phi2 psub)
           method fiff phi1 phi2 psub = mk_iff (phi1 psub) (phi2 psub)
           method fxor phi1 phi2 psub = mk_xor (phi1 psub) (phi2 psub)
           method fbind binder senv phi1 psub = mk_bind binder senv (phi1 psub)

           method fletrec funcs phi1 psub =
             let psub =
               Map.remove_keys psub (List.map funcs ~f:(fun def -> def.name))
             in
             mk_letrec (map_funcs funcs ~f:(fun phi -> phi psub)) (phi1 psub)

           method flet tvar sort def body psub =
             mk_let_formula tvar sort (Term.subst_preds psub def) (body psub)
        end)
      phi psub

  let subst_funcs fsub phi =
    fold
      ~f:
        (object
           method fatom atom fsub = mk_atom @@ Atom.subst_funcs fsub atom
           method fnot phi1 fsub = mk_neg (phi1 fsub)
           method fand phi1 phi2 fsub = mk_and (phi1 fsub) (phi2 fsub)
           method for_ phi1 phi2 fsub = mk_or (phi1 fsub) (phi2 fsub)
           method fimply phi1 phi2 fsub = mk_imply (phi1 fsub) (phi2 fsub)
           method fiff phi1 phi2 fsub = mk_iff (phi1 fsub) (phi2 fsub)
           method fxor phi1 phi2 fsub = mk_xor (phi1 fsub) (phi2 fsub)

           method fbind binder senv phi1 fsub =
             let fsub = Map.remove_keys fsub (List.map ~f:fst senv) in
             mk_bind binder senv (phi1 fsub)

           method fletrec funcs phi1 fsub =
             mk_letrec (map_funcs funcs ~f:(fun phi -> phi fsub)) (phi1 fsub)

           method flet tvar sort def body fsub =
             let fsub' = Map.Poly.remove fsub tvar in
             mk_let_formula tvar sort (Term.subst_funcs fsub def) (body fsub')
        end)
      phi fsub

  let rec subst_neg pvar = function
    | Atom (Atom.App (Predicate.Var (pvar', sort), args, info), info') ->
        let atom = Atom.App (Predicate.Var (pvar', sort), args, info) in
        if Stdlib.(pvar = pvar') then UnaryOp (Not, Atom (atom, info), Dummy)
        else Atom (Atom.subst_neg pvar atom, info')
    | Atom (atom, info) -> Atom (Atom.subst_neg pvar atom, info)
    | UnaryOp (Not, phi, info) -> (
        match subst_neg pvar phi with
        | UnaryOp (Not, phi', _) -> phi'
        | phi' -> UnaryOp (Not, phi', info))
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, subst_neg pvar phi1, subst_neg pvar phi2, info)
    | Bind (binder, bounds, body, info) ->
        Bind (binder, bounds, subst_neg pvar body, info)
    | LetRec (funcs, body, info) ->
        LetRec (map_funcs funcs ~f:(subst_neg pvar), subst_neg pvar body, info)
    | LetFormula (var, sort, dec, body, info) ->
        LetFormula (var, sort, dec, subst_neg pvar body, info)

  let aconv_tvar =
    fold
      ~f:
        (object
           method fatom atom = mk_atom (Atom.aconv_tvar atom)
           method fnot phi1 = mk_neg phi1
           method fand phi1 phi2 = mk_and phi1 phi2
           method for_ phi1 phi2 = mk_or phi1 phi2
           method fimply phi1 phi2 = mk_imply phi1 phi2
           method fiff phi1 phi2 = mk_iff phi1 phi2
           method fxor phi1 phi2 = mk_xor phi1 phi2

           method fbind binder senv phi1 =
             let senv', ren = refresh_sort_env_list senv in
             mk_bind binder senv' (rename ren phi1)

           method fletrec funcs phi1 =
             let funcs' =
               List.map funcs ~f:(fun def ->
                   let args, ren = refresh_sort_env_list def.args in
                   { def with args; body = Formula.rename ren def.body })
             in
             mk_letrec funcs' phi1

           method flet x sort def body =
             mk_let_formula x sort (Term.aconv_tvar def) body
        end)

  let aconv_tvar_norm next =
    fold
      ~f:
        (object
           method fatom atom = mk_atom (Atom.aconv_tvar_norm next atom)
           method fnot phi1 = mk_neg phi1
           method fand phi1 phi2 = mk_and phi1 phi2
           method for_ phi1 phi2 = mk_or phi1 phi2
           method fimply phi1 phi2 = mk_imply phi1 phi2
           method fiff phi1 phi2 = mk_iff phi1 phi2
           method fxor phi1 phi2 = mk_xor phi1 phi2

           method fbind binder senv phi1 =
             let senv', map = refresh_sort_env_list_norm next senv in
             mk_bind binder senv' (rename map phi1)

           method fletrec funcs phi1 =
             let funcs' =
               List.map funcs ~f:(fun def ->
                   let args, ren = refresh_sort_env_list_norm next def.args in
                   { def with args; body = Formula.rename ren def.body })
             in
             mk_letrec funcs' phi1

           method flet x sort def body =
             mk_let_formula x sort (Term.aconv_tvar_norm next def) body
        end)

  let aconv_pvar =
    fold
      ~f:
        (object
           method fatom atom = mk_atom (Atom.aconv_pvar atom)
           method fnot phi1 = mk_neg phi1
           method fand phi1 phi2 = mk_and phi1 phi2
           method for_ phi1 phi2 = mk_or phi1 phi2
           method fimply phi1 phi2 = mk_imply phi1 phi2
           method fiff phi1 phi2 = mk_iff phi1 phi2
           method fxor phi1 phi2 = mk_xor phi1 phi2

           method fbind binder senv phi1 =
             mk_bind binder senv phi1 (* ToDo: fix bug? *)

           method fletrec funcs phi1 =
             let ren =
               Map.Poly.of_alist_exn
               @@ List.map funcs ~f:(fun def ->
                      (def.name, Ident.mk_fresh_pvar ()))
             in
             let funcs' =
               List.map funcs ~f:(fun def ->
                   {
                     def with
                     name = Map.Poly.find_exn ren def.name;
                     body = rename_pvars ren def.body;
                   })
             in
             mk_letrec funcs' @@ rename_pvars ren phi1

           method flet x sort def body =
             mk_let_formula x sort (Term.aconv_pvar def) body
        end)

  let rec subst_sorts map = function
    | Atom (atom, info) -> Atom (Atom.subst_sorts map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, subst_sorts map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, subst_sorts map phi1, subst_sorts map phi2, info)
    | Bind (Random rand, bounds, phi, info) ->
        Bind
          ( Random (Rand.subst_sorts map rand),
            subst_sorts_bounds map bounds,
            subst_sorts map phi,
            info )
    | Bind (binder, bounds, phi, info) ->
        Bind (binder, subst_sorts_bounds map bounds, subst_sorts map phi, info)
    | LetRec (funcs, phi, info) ->
        let funcs' =
          List.map funcs ~f:(fun def ->
              {
                def with
                args = subst_sorts_bounds map def.args;
                body = subst_sorts map def.body;
              })
        in
        LetRec (funcs', subst_sorts map phi, info)
    | LetFormula (var, sort, def, body, info) ->
        LetFormula
          ( var,
            Term.subst_sorts_sort map sort,
            Term.subst_sorts map def,
            subst_sorts map body,
            info )

  let rec subst_conts map = function
    | Atom (atom, info) -> Atom (Atom.subst_conts map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, subst_conts map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, subst_conts map phi1, subst_conts map phi2, info)
    | Bind (Random rand, bounds, phi, info) ->
        let bounds' =
          List.map bounds ~f:(fun (x, s) -> (x, Term.subst_conts_sort map s))
        in
        Bind
          ( Random (Rand.subst_conts map rand),
            bounds',
            subst_conts map phi,
            info )
    | Bind (binder, bounds, phi, info) ->
        Bind (binder, subst_conts_bounds map bounds, subst_conts map phi, info)
    | LetRec (funcs, phi, info) ->
        let funcs' =
          List.map funcs ~f:(fun def ->
              {
                def with
                args = subst_conts_bounds map def.args;
                body = subst_conts map def.body;
              })
        in
        LetRec (funcs', subst_conts map phi, info)
    | LetFormula (var, sort, def, body, info) ->
        LetFormula
          ( var,
            Term.subst_conts_sort map sort,
            Term.subst_conts map def,
            subst_conts map body,
            info )

  let rec subst_opsigs map = function
    | Atom (atom, info) -> Atom (Atom.subst_opsigs map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, subst_opsigs map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, subst_opsigs map phi1, subst_opsigs map phi2, info)
    | Bind (Random rand, bounds, phi, info) ->
        let bounds' =
          List.map bounds ~f:(fun (x, s) -> (x, Term.subst_opsigs_sort map s))
        in
        Bind
          ( Random (Rand.subst_opsigs map rand),
            bounds',
            subst_opsigs map phi,
            info )
    | Bind (binder, bounds, phi, info) ->
        Bind (binder, subst_opsigs_bounds map bounds, subst_opsigs map phi, info)
    | LetRec (funcs, phi, info) ->
        let funcs' =
          List.map funcs ~f:(fun def ->
              {
                def with
                args = subst_opsigs_bounds map def.args;
                body = subst_opsigs map def.body;
              })
        in
        LetRec (funcs', subst_opsigs map phi, info)
    | LetFormula (var, sort, def, body, info) ->
        LetFormula
          ( var,
            Term.subst_opsigs_sort map sort,
            Term.subst_opsigs map def,
            subst_opsigs map body,
            info )

  let subst_sorts_pred sub (x, phi) = (x, subst_sorts sub phi)
  let apply_pred (x, phi) t = subst (Map.Poly.singleton x t) phi

  (** Construction *)

  let insert_let_formula var sort def info phi =
    if Set.mem (Formula.tvs_of phi) var then
      let var' = Ident.mk_fresh_tvar () in
      LetFormula
        (var', sort, def, rename (Map.Poly.singleton var var') phi, info)
    else phi

  (** Transformation *)

  let reduce_sort_map (senv, phi) =
    let fvs = fvs_of phi in
    (Map.Poly.filter_keys senv ~f:(Set.mem fvs), phi)
  (*let refresh_tvar (phi: Formula.t) =
    let map =
      Map.of_set_exn @@
      Set.Poly.map ~f:(fun (t, s) -> (t, Term.mk_fresh_var s)) @@
      term_sort_env_of phi in
    Formula.subst map phi*)

  let complete_psort map = map_atom ~f:(Atom.complete_psort map >> mk_atom)
  (*ToDo:support LetRec*)

  let rec complete_tsort map = function
    | Atom (atom, info) -> Atom (Atom.subst map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, complete_tsort map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, complete_tsort map phi1, complete_tsort map phi2, info)
    | Bind (binder, args, phi, info) ->
        let map' =
          Set.fold ~init:map (Set.Poly.of_list args) ~f:(fun map (x, sort) ->
              Map.Poly.update map x ~f:(fun _ -> Term.mk_var x sort))
        in
        Bind (binder, args, complete_tsort map' phi, info)
    | LetRec _ -> failwith "LetRec in this position is not supported."
    | LetFormula (var, sort, def, body, info) ->
        of_bool_term @@ Term.complete_tsort map
        @@ Term.LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec rm_quant ?(forall = true) = function
    | Atom (atom, info) -> (Set.Poly.empty, Atom (atom, info))
    | UnaryOp (Not, phi, info) ->
        let senv, phi' = rm_quant ~forall:(not forall) phi in
        (senv, UnaryOp (Not, phi', info))
    | BinaryOp (((And | Or) as op), phi1, phi2, info) ->
        let senv1, phi1' = rm_quant ~forall phi1 in
        let senv2, phi2' = rm_quant ~forall phi2 in
        (Set.union senv1 senv2, BinaryOp (op, phi1', phi2', info))
    | BinaryOp (Imply, phi1, phi2, info) ->
        let senv1, phi1' = rm_quant ~forall:(not forall) phi1 in
        let senv2, phi2' = rm_quant ~forall phi2 in
        (Set.union senv1 senv2, BinaryOp (Imply, phi1', phi2', info))
    | BinaryOp ((Xor | Iff), _phi1, _phi2, _info) ->
        failwith "not supported @ 1"
    | Bind (Forall, senv, phi, _) ->
        if forall then
          let senv', phi' = rm_quant ~forall phi in
          (Set.union (Set.Poly.of_list senv) senv', phi')
        else
          (Set.Poly.empty, mk_forall senv phi (*failwith "not supported @ 2"*))
    | Bind (Exists, senv, phi, _) ->
        if not forall then
          let senv', phi' = rm_quant ~forall phi in
          (Set.union (Set.Poly.of_list senv) senv', phi')
        else
          (Set.Poly.empty, mk_exists senv phi (*failwith "not supported @ 3"*))
    | Bind (_, _, _, _) -> failwith "unimplemented"
    | LetRec (_, _, _) -> failwith "unimplemented"
    | LetFormula (var, sort, def, body, info) ->
        (* ToDo: assume there is no quantifiers in def *)
        let senv, body' = rm_quant ~forall body in
        (senv, LetFormula (var, sort, def, body', info))

  (** ToDo: this seems not capture avoiding *)
  let move_quantifiers_to_front fml =
    let rec rename_in_formula used_names replace_env fml =
      if is_atom fml then
        let atom, info = let_atom fml in
        let atom = rename_in_atom replace_env atom in
        (mk_atom atom ~info, used_names, replace_env)
      else if is_binop fml then
        let binop, left, right, info = let_binop fml in
        let left, used_names, replace_env =
          rename_in_formula used_names replace_env left
        in
        let right, used_names, replace_env =
          rename_in_formula used_names replace_env right
        in
        (mk_binop binop left right ~info, used_names, replace_env)
      else if is_unop fml then
        let unop, body, info = let_unop fml in
        let body, used_names, replace_env =
          rename_in_formula used_names replace_env body
        in
        (mk_unop unop body ~info, used_names, replace_env)
      else if is_bind fml then
        let binder, bounds, body, info = let_bind fml in
        let new_bounds =
          List.map bounds ~f:(fun (tvar, sort) ->
              let var_name = ref (Ident.name_of_tvar tvar ^ "#q") in
              while Map.Poly.mem used_names !var_name do
                var_name := !var_name ^ "'"
              done;
              (Ident.Tvar !var_name, sort))
        in
        let new_bound_tvars, _ = List.unzip new_bounds in
        let bound_tvars = List.map ~f:fst bounds in
        let used_names =
          Map.update_with used_names
            (Map.Poly.of_alist_exn
            @@ List.map bound_tvars ~f:(fun tvar ->
                   (Ident.name_of_tvar tvar, ())))
        in
        let replace_env =
          Map.update_with replace_env
            (Map.Poly.of_alist_exn @@ List.zip_exn bound_tvars new_bound_tvars)
        in
        let body, used_names, replace_env =
          rename_in_formula used_names replace_env body
        in
        (mk_bind binder new_bounds body ~info, used_names, replace_env)
      else assert false
    and rename_in_atom replace_env atom =
      if Atom.is_true atom || Atom.is_false atom then atom
      else if Atom.is_app atom then
        let pred, args, info = Atom.let_app atom in
        let pred = rename_in_predicate pred in
        let args = List.map ~f:(rename_in_term replace_env) args in
        Atom.mk_app pred args ~info
      else assert false
    and rename_in_predicate pred =
      if Predicate.is_fix pred then
        let def = Predicate.let_fix pred in
        Predicate.Fixpoint { def with body = rename def.body }
      else if Predicate.is_psym pred || Predicate.is_var pred then pred
      else assert false
    and rename_in_term replace_env term =
      if Term.is_var term then
        let (tvar, sort), info = Term.let_var term in
        Term.mk_var (Map.Poly.find_exn replace_env tvar) sort ~info
      else if Term.is_app term then
        let funsym, args, info = Term.let_app term in
        Term.mk_fsym_app funsym
          (List.map ~f:(rename_in_term replace_env) args)
          ~info
      else assert false
    and rename fml =
      let fv = Set.to_list @@ tvs_of fml in
      (* let fv_names = (List.map ~f:(fun tvar -> (Ident.name_of_tvar tvar, ())) fv) in *)
      let fml, _, _ =
        rename_in_formula Map.Poly.empty
          (Map.Poly.of_alist_exn @@ List.zip_exn fv fv)
          fml
      in
      fml
    in
    let mk_bind binder bounds fml =
      if List.is_empty bounds then fml else mk_bind binder bounds fml
    in
    let rec move_to_front_in_formula fml =
      if is_atom fml then
        let atom, info = let_atom fml in
        (mk_atom (move_to_front_in_atom atom) ~info, [], [])
      else if is_neg fml then
        let negop, fml, info = let_unop fml in
        let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
        (mk_unop negop fml ~info, exists_bounds, forall_bounds)
      else if is_imply fml then
        (* TODO *)
        failwith (*str_of fml ^*) " not supported\n"
      else if is_iff fml then
        (* TODO *)
        failwith (*str_of fml ^*) " not supported\n"
      else if is_and fml || is_or fml then
        let binop, left_fml, right_fml, info = let_binop fml in
        let left_fml, left_forall_bounds, left_exists_bounds =
          move_to_front_in_formula left_fml
        in
        let right_fml, right_forall_bounds, right_exists_bounds =
          move_to_front_in_formula right_fml
        in
        ( mk_binop binop left_fml right_fml ~info,
          left_forall_bounds @ right_forall_bounds,
          left_exists_bounds @ right_exists_bounds )
      else if is_bind fml then
        let binder, bounds, fml, _ = let_bind fml in
        let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
        let binder_bounds, another_bounds =
          match binder with
          | Forall -> (forall_bounds, exists_bounds)
          | Exists -> (exists_bounds, forall_bounds)
          | Random _ -> assert false
        in
        let fml = mk_bind (flip_quantifier binder) another_bounds fml in
        let another_bounds = [] in
        let binder_bounds = bounds @ binder_bounds in
        let forall_bounds, exists_bounds =
          match binder with
          | Forall -> (binder_bounds, another_bounds)
          | Exists -> (another_bounds, binder_bounds)
          | Random _ -> assert false
        in
        (fml, forall_bounds, exists_bounds)
      else assert false
    and move_to_front_in_atom atom =
      if Atom.is_app atom then
        let pred, args, info = Atom.let_app atom in
        Atom.mk_app (move_to_front_in_predicate pred) args ~info
      else if Atom.is_true atom || Atom.is_false atom then atom
      else assert false
    and move_to_front_in_predicate pred =
      if Predicate.is_fix pred then
        let def = Predicate.let_fix pred in
        Predicate.Fixpoint { def with body = move_to_front def.body }
      else if Predicate.is_psym pred || Predicate.is_var pred then pred
      else assert false
    and move_to_front fml =
      let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
      mk_bind Forall forall_bounds @@ mk_bind Exists exists_bounds fml
    in
    move_to_front @@ rename fml

  let elim_neq = map_atom ~f:Atom.elim_neq
  let elim_ite = map_atom ~f:Atom.elim_ite

  let elim_pvars unknowns =
    map_atom ~f:(function
      | Atom.App (Predicate.Var (pvar, []), [], _) as atom ->
          if Set.mem unknowns (Ident.pvar_to_tvar pvar) then mk_atom atom
          else of_bool_term (Term.mk_var (Ident.pvar_to_tvar pvar) T_bool.SBool)
      | Atom.App (pred, args, _) ->
          mk_atom @@ Atom.mk_app pred
          @@ List.map args ~f:(Term.elim_pvars unknowns)
      | (Atom.True _ | Atom.False _) as atom -> mk_atom atom)

  (** eliminate let-binding that contains an unknown to be synthesized *)
  let rec elim_let_with_unknowns ?(map = Map.Poly.empty) unknowns = function
    | LetFormula (var, sort, def, body, info) ->
        let def' = Term.elim_let_with_unknowns ~map unknowns def in
        if Set.disjoint (Term.fvs_of def') unknowns then
          LetFormula
            (var, sort, def', elim_let_with_unknowns ~map unknowns body, info)
        else
          elim_let_with_unknowns
            ~map:(Map.Poly.set map ~key:var ~data:def')
            unknowns body
    | UnaryOp (op, phi1, info) ->
        UnaryOp (op, elim_let_with_unknowns ~map unknowns phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp
          ( op,
            elim_let_with_unknowns ~map unknowns phi1,
            elim_let_with_unknowns ~map unknowns phi2,
            info )
    | Bind (bin, senv, phi1, info) ->
        let bounds = Set.Poly.of_list @@ List.map ~f:fst senv in
        let map' = Map.Poly.filter_keys map ~f:(Fn.non @@ Set.mem bounds) in
        Bind (bin, senv, elim_let_with_unknowns ~map:map' unknowns phi1, info)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _) as phi -> (
        match Map.Poly.find map (Ident.Tvar var) with
        | Some t -> of_bool_term t
        | None -> phi)
    | Atom (Atom.App (pred, args, info), info') ->
        Atom
          ( Atom.App
              ( pred,
                List.map args ~f:(Term.elim_let_with_unknowns ~map unknowns),
                info ),
            info' )
    | Atom (((Atom.True _ | Atom.False _) as atom), info) -> Atom (atom, info)
    | LetRec _ -> failwith "unimplemented"

  let rec elim_let ?(map = Map.Poly.empty) = function
    | LetFormula (var, _, def, body, _) ->
        let def' = Term.elim_let ~map def in
        elim_let ~map:(Map.Poly.set map ~key:var ~data:def') body
    | UnaryOp (op, phi1, info) -> UnaryOp (op, elim_let ~map phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, elim_let ~map phi1, elim_let ~map phi2, info)
    | Bind (bin, senv, phi1, info) ->
        let bounds = Set.Poly.of_list @@ List.map ~f:fst senv in
        let map' = Map.Poly.filter_keys map ~f:(Fn.non @@ Set.mem bounds) in
        Bind (bin, senv, elim_let ~map:map' phi1, info)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _) as phi -> (
        match Map.Poly.find map (Ident.Tvar var) with
        | Some t -> of_bool_term t
        | None -> phi)
    | Atom (Atom.App (pred, args, info), info') ->
        Atom
          (Atom.App (pred, List.map args ~f:(Term.elim_let ~map), info), info')
    | Atom (((Atom.True _ | Atom.False _) as atom), info) -> Atom (atom, info)
    | LetRec _ -> failwith "unimplemented"

  let rec elim_unused_bounds = function
    | LetFormula (var, sort, def, body, info) ->
        LetFormula (var, sort, def, elim_unused_bounds body, info)
    | UnaryOp (op, phi1, info) -> UnaryOp (op, elim_unused_bounds phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, elim_unused_bounds phi1, elim_unused_bounds phi2, info)
    | Bind (binder, bounds, phi1, info) ->
        let phi1 = elim_unused_bounds phi1 in
        let ftv = tvs_of phi1 in
        let bounds = List.filter ~f:(fst >> Set.mem ftv) bounds in
        mk_bind_if_bounded binder bounds phi1 ~info
    | Atom (_, _) as phi -> phi (* TODO *)
    | LetRec _ -> failwith "unimplemented"

  (* assume that the argument is normalized and alpha-renamed *)
  let rec elim_let_equisat = function
    | LetFormula (var, sort, def, body, _) ->
        let senv, body = elim_let_equisat body in
        ( Map.Poly.add_exn senv ~key:var ~data:sort,
          mk_and (eq (Term.mk_var var sort) def) body )
    | UnaryOp (Not, phi1, info) ->
        let senv, phi1 = elim_let_equivalid phi1 in
        (senv, UnaryOp (Not, phi1, info))
    | BinaryOp (Imply, phi1, phi2, info) ->
        let senv1, phi1 = elim_let_equivalid phi1 in
        let senv2, phi2 = elim_let_equisat phi2 in
        (Map.force_merge senv1 senv2, BinaryOp (Imply, phi1, phi2, info))
    | BinaryOp ((Iff | Xor), _phi1, _phi2, _info) as phi ->
        ( Map.Poly.empty,
          phi (* assume that phi does not contain a let-expression*) )
    | BinaryOp (((And | Or) as op), phi1, phi2, info) ->
        let senv1, phi1 = elim_let_equisat phi1 in
        let senv2, phi2 = elim_let_equisat phi2 in
        (Map.force_merge senv1 senv2, BinaryOp (op, phi1, phi2, info))
    | Bind (binder, bounds, phi1, info) ->
        let senv, phi1 = elim_let_equisat phi1 in
        (senv, mk_bind_if_bounded binder bounds phi1 ~info)
    | Atom (_, _) as phi -> (Map.Poly.empty, phi)
    | LetRec _ -> failwith "unimplemented"

  (* assume that the argument is normalized and alpha-renamed *)
  and elim_let_equivalid = function
    | LetFormula (var, sort, def, body, _) ->
        let senv, body = elim_let_equivalid body in
        ( Map.Poly.add_exn senv ~key:var ~data:sort,
          mk_or (neq (Term.mk_var var sort) def) body )
    | UnaryOp (Not, phi1, info) ->
        let senv, phi1 = elim_let_equisat phi1 in
        (senv, UnaryOp (Not, phi1, info))
    | BinaryOp (Imply, phi1, phi2, info) ->
        let senv1, phi1 = elim_let_equisat phi1 in
        let senv2, phi2 = elim_let_equivalid phi2 in
        (Map.force_merge senv1 senv2, BinaryOp (Imply, phi1, phi2, info))
    | BinaryOp ((Iff | Xor), _phi1, _phi2, _info) as phi ->
        ( Map.Poly.empty,
          phi (* assume that phi does not contain a let-expression*) )
    | BinaryOp (((And | Or) as op), phi1, phi2, info) ->
        let senv1, phi1 = elim_let_equivalid phi1 in
        let senv2, phi2 = elim_let_equivalid phi2 in
        (Map.force_merge senv1 senv2, BinaryOp (op, phi1, phi2, info))
    | Bind (binder, bounds, phi1, info) ->
        let senv, phi1 = elim_let_equivalid phi1 in
        (senv, mk_bind_if_bounded binder bounds phi1 ~info)
    | Atom (_, _) as phi -> (Map.Poly.empty, phi)
    | LetRec _ -> failwith "unimplemented"

  (* assume that [phi] is normalized and alpha-renamed *)
  let elim_let_equi is_forall phi =
    if is_forall then
      let senv, phi = elim_let_equivalid phi in
      forall (Map.Poly.to_alist senv) phi
    else
      let senv, phi = elim_let_equisat phi in
      exists (Map.Poly.to_alist senv) phi

  let extend_pred_params pvar extended_params =
    map_atom ~f:(Atom.extend_pred_params pvar extended_params >> mk_atom)

  let instantiate_div0_mod0 = map_atom ~f:(Atom.instantiate_div0_mod0 >> mk_atom)
  let replace_div_mod map = map_atom ~f:(Atom.replace_div_mod map >> mk_atom)

  (* Prerequisites of rm_div_mod f
     f is normalized and a-converted, and there are no free variables in f
     there are some unsupported forms such as:
       (exists x. x=0 and z = x mod 0) and (exists y. y=0 and z = y mod 0)
     if f is prenex normal form there is no problem *)
  (* simplify assumes that rm_div_mod is already applied *)
  let rm_div_mod f =
    let divmod = div_rem_of f in
    if Set.is_empty divmod then f
    else
      let map =
        Set.to_map divmod
          ~f:Ident.(fun _ -> (mk_fresh_tvar (), mk_fresh_tvar ()))
      in
      let f = replace_div_mod map f in
      let newmap =
        Map.rename_keys map ~f:(fun (t1, t2) ->
            Some (Term.replace_div_mod map t1, Term.replace_div_mod map t2))
      in
      let make_check_zero ((e1, n1), (d1, m1)) ((e2, n2), (d2, m2)) =
        let atom1 = Formula.mk_and (Formula.eq e1 e2) (Formula.eq n1 n2) in
        let atom2 =
          Formula.mk_and
            (Formula.eq (Term.mk_var d1 T_int.SInt) (Term.mk_var d2 T_int.SInt))
            (Formula.eq (Term.mk_var m1 T_int.SInt) (Term.mk_var m2 T_int.SInt))
        in
        Formula.mk_imply atom1 atom2
      in
      let check_zero outerlist innerlist =
        List.fold innerlist
          ~init:(Formula.mk_true (), outerlist)
          ~f:(fun (acc, outerlist) a ->
            ( Formula.and_of (acc :: List.map outerlist ~f:(make_check_zero a)),
              a :: outerlist ))
      in
      let make_restriction mapouter mapinner =
        let outerlist = Map.Poly.to_alist mapouter in
        let innerlist = Map.Poly.to_alist mapinner in
        let f1 =
          Formula.and_of
          @@ List.map innerlist ~f:(fun ((e, n), (d, m)) ->
                 let atom1 = Formula.neq n (T_int.zero ()) in
                 let atom2 =
                   Formula.eq e
                     (T_int.mk_add
                        (T_int.mk_mul n (Term.mk_var d T_int.SInt))
                        (Term.mk_var m T_int.SInt))
                 in
                 let atom3 =
                   Formula.leq (T_int.zero ()) (Term.mk_var m T_int.SInt)
                 in
                 let atom4 =
                   Formula.lt (Term.mk_var m T_int.SInt) (T_int.mk_abs n)
                 in
                 Formula.mk_imply atom1 (Formula.and_of [ atom2; atom3; atom4 ]))
        in
        let f2, newlist = check_zero outerlist innerlist in
        (Formula.mk_and f1 f2, Map.Poly.of_alist_exn newlist)
      in
      let rec divide_map map1 map2 vars =
        let map21, map22 =
          Map.Poly.partitioni_tf map2 ~f:(fun ~key:(t1, t2) ~data:_ ->
              let varset = Set.union (Term.tvs_of t1) (Term.tvs_of t2) in
              Set.is_subset varset ~of_:vars)
        in
        if Map.Poly.is_empty map21 then (map1, map2, vars)
        else
          let newvars =
            Map.Poly.fold map21 ~init:Set.Poly.empty
              ~f:(fun ~key:_ ~data:(d, m) newvars ->
                Set.add (Set.add newvars d) m)
          in
          divide_map (Map.force_merge map1 map21) map22 (Set.union vars newvars)
      in
      let rec add_restriction mapouter mapinner vars = function
        | Atom (atom, info) -> Atom (atom, info)
        | UnaryOp (op, phi, info) ->
            UnaryOp (op, add_restriction mapouter mapinner vars phi, info)
        | BinaryOp (op, phi1, phi2, info) ->
            BinaryOp
              ( op,
                add_restriction mapouter mapinner vars phi1,
                add_restriction mapouter mapinner vars phi2,
                info )
        | Bind (binder, bounds, phi, info) ->
            let newvars, _ = List.unzip bounds in
            let newvars = Set.union vars (Set.Poly.of_list newvars) in
            let map1, map2, newvars =
              divide_map Map.Poly.empty mapinner newvars
            in
            let restriction, newmap = make_restriction mapouter map1 in
            let sortenv =
              Map.Poly.fold map1 ~init:[] ~f:(fun ~key:_ ~data:(d, m) l ->
                  (d, T_int.SInt) :: (m, T_int.SInt) :: l)
            in
            let f =
              Formula.mk_exists sortenv
              @@ Formula.mk_and restriction
                   (add_restriction newmap map2 newvars phi)
            in
            Bind (binder, bounds, f, info)
        | LetFormula (var, sort, def, body, info) ->
            LetFormula
              (var, sort, def, add_restriction mapouter mapinner vars body, info)
        | LetRec (_, _, _) -> failwith "unimplemented"
      in
      let map1, map2, vars = divide_map Map.Poly.empty newmap Set.Poly.empty in
      let init, _ = make_restriction Map.Poly.empty map1 in
      let sortenv =
        Map.Poly.fold map1 ~init:[] ~f:(fun ~key:_ ~data:(d, m) l ->
            (d, T_int.SInt) :: (m, T_int.SInt) :: l)
      in
      Formula.mk_exists sortenv
      @@ Formula.mk_and init (add_restriction map1 map2 vars f)

  let rec rm_atom ?(polarity = true) ?(is_and = true) ~f = function
    | Atom (atom, info) ->
        let polarity = if is_and then polarity else not polarity in
        if f atom then if polarity then mk_true () else mk_false ()
        else Atom (atom, info)
    | UnaryOp (Not, phi, info) ->
        UnaryOp (Not, rm_atom ~polarity:(not polarity) ~is_and ~f phi, info)
    | BinaryOp (And, phi1, phi2, info) ->
        BinaryOp
          ( And,
            rm_atom ~polarity ~is_and:true ~f phi1,
            rm_atom ~polarity ~is_and:true ~f phi2,
            info )
    | BinaryOp (Or, phi1, phi2, info) ->
        BinaryOp
          ( Or,
            rm_atom ~polarity ~is_and:false ~f phi1,
            rm_atom ~polarity ~is_and:false ~f phi2,
            info )
    | Bind (binder, bounded, phi, info) ->
        Bind (binder, bounded, rm_atom ~polarity ~is_and ~f phi, info)
    | phi -> phi

  let rec to_atom = function
    | Atom (atom, _) -> atom
    | UnaryOp (Not, Atom (atom, _), _) -> (
        match Atom.negate atom with
        | None -> failwith "to_atom"
        | Some atm -> atm)
    | UnaryOp (Not, UnaryOp (Not, phi', _), _) -> to_atom phi'
    | phi -> failwith (Formula.str_of phi ^ " is not atomic formula")

  let univ_clos phi =
    let bounds = Set.to_list @@ term_sort_env_of phi in
    if List.is_empty bounds then phi else mk_forall bounds phi

  (* assume the input is alpha-converted *)
  let rec split_exists = function
    | Bind (Exists, senv1, phi, _) ->
        let senv2, phi = split_exists phi in
        (senv1 @ senv2, phi)
    | phi -> ([], phi)

  (* assume the input is alpha-converted and in NNF *)
  let rec split_quantifiers = function
    | Atom (App (pred, tl, _), _) ->
        let qs, termlist =
          (* ToDo: the following seems not correct *)
          List.fold tl ~init:([], []) ~f:(fun (qs, terms) -> function
            | FunApp (T_bool.Formula phi, [], _) ->
                let q, phi = split_quantifiers phi in
                (qs @ q, terms @ [ T_bool.of_formula phi ])
            | term -> (qs, terms @ [ term ]))
        in
        (qs, mk_atom @@ Atom.mk_app pred termlist)
    | Atom (_, _) as phi -> ([], phi)
    | UnaryOp (unop, phi, _) ->
        (* ToDo: correct? *)
        let qs, phi = split_quantifiers phi in
        (qs, mk_unop unop phi)
    | BinaryOp (binop, phi1, phi2, _) ->
        let qs1, phi1 = split_quantifiers phi1 in
        let qs2, phi2 = split_quantifiers phi2 in
        (qs1 @ qs2, mk_binop binop phi1 phi2)
    | Bind (binder, sortenv, phi, _) ->
        let qs, phi = split_quantifiers phi in
        ((binder, sortenv) :: qs, phi)
    | LetRec (_, _, _) -> assert false
    | LetFormula _ -> failwith @@ "'LetFormula' is not supported yet" (* TODO *)

  let rec nnf_of = function
    | Atom (_, _) as phi -> phi
    | UnaryOp (Not, Atom (Atom.True _, _), _) -> mk_false ()
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
    | UnaryOp (Not, LetRec ([], phi, _), _) -> nnf_of (mk_neg phi)
    | BinaryOp (And, phi1, phi2, _) -> mk_and (nnf_of phi1) (nnf_of phi2)
    | BinaryOp (Or, phi1, phi2, _) -> mk_or (nnf_of phi1) (nnf_of phi2)
    | BinaryOp (Imply, phi1, phi2, _) ->
        mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2)
    | BinaryOp (Iff, phi1, phi2, _) -> mk_iff (nnf_of phi1) (nnf_of phi2)
    | BinaryOp (Xor, phi1, phi2, _) -> mk_xor (nnf_of phi1) (nnf_of phi2)
    | Bind (b, params, phi, _) -> mk_bind b params (nnf_of phi)
    | LetRec ([], phi, _) -> nnf_of phi
    | LetFormula (var, sort, def, body, info) ->
        LetFormula (var, sort, def, nnf_of body, info)
    | phi -> failwith ("Unexpected formula in nnf_of: " ^ Formula.str_of phi)

  let rec dnf_of_aux ?(process_pure = false) exi_senv senv = function
    | Atom (Atom.True _, _) | UnaryOp (Not, Atom (Atom.False _, _), _) ->
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | Atom (Atom.False _, _) | UnaryOp (Not, Atom (Atom.True _, _), _) ->
        Set.Poly.empty
    | phi
      when (not process_pure)
           && Set.disjoint (fvs_of phi) (Map.key_set exi_senv) ->
        Set.Poly.singleton
          (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
    | Atom ((Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom), _)
      -> (
        let tvar = Ident.Tvar name in
        match (Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar) with
        | Some _, None ->
            Set.Poly.singleton
              (Set.Poly.singleton atom, Set.Poly.empty, Set.Poly.empty)
        | None, Some _ ->
            Set.Poly.singleton
              (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
        | _ -> failwith "dnf_of")
    | UnaryOp
        ( Not,
          Atom ((Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom), _),
          _ ) -> (
        let tvar = Ident.Tvar name in
        match (Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar) with
        | Some _, None ->
            Set.Poly.singleton
              (Set.Poly.empty, Set.Poly.singleton atom, Set.Poly.empty)
        | None, Some _ ->
            Set.Poly.singleton
              ( Set.Poly.empty,
                Set.Poly.empty,
                Set.Poly.singleton (mk_neg (mk_atom atom)) )
        | _ -> failwith "cnf_of")
    | Atom ((Atom.App (Predicate.Psym _, _, _) as atom), _) ->
        (* not reachable *)
        Set.Poly.singleton
          (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
    | UnaryOp (Not, Atom ((Atom.App (Predicate.Psym _, _, _) as atom), _), _) ->
        (* not reachable *)
        Set.Poly.singleton
          ( Set.Poly.empty,
            Set.Poly.empty,
            Set.Poly.singleton (mk_neg (mk_atom atom)) )
    | UnaryOp (Not, _, _) -> assert false
    | Atom (Atom.App (Predicate.Fixpoint _, _, _), _) ->
        failwith "not supported"
    | BinaryOp (And, phi1, phi2, _) ->
        let cls1 = dnf_of_aux ~process_pure exi_senv senv phi1 in
        let cls2 = dnf_of_aux ~process_pure exi_senv senv phi2 in
        Set.cartesian_map cls1 cls2
          ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
            (Set.union ps1 ps2, Set.union ns1 ns2, Set.union phis1 phis2))
    | BinaryOp (Or, phi1, phi2, _) ->
        let cls1 = dnf_of_aux ~process_pure exi_senv senv phi1 in
        let cls2 = dnf_of_aux ~process_pure exi_senv senv phi2 in
        let phis, cls =
          Set.union cls1 cls2
          |> Set.partition_tf ~f:(fun (ps, ns, phis) ->
                 Set.is_empty ps && Set.is_empty ns
                 && Set.is_empty
                    @@ Set.inter (Map.key_set exi_senv)
                         (fvs_of @@ and_of @@ Set.to_list phis))
          |> Pair.map
               (Set.Poly.map ~f:(Triple.trd >> Set.to_list >> and_of))
               Fn.id
        in
        if Set.is_empty phis then cls
        else if process_pure then
          Set.union cls
          @@ Set.Poly.map phis ~f:(fun phi ->
                 (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi))
        else
          Set.add cls
            ( Set.Poly.empty,
              Set.Poly.empty,
              Set.Poly.singleton @@ or_of @@ Set.to_list phis )
    | BinaryOp (Imply, phi1, phi2, _) ->
        dnf_of_aux ~process_pure exi_senv senv
        @@ mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2)
    | BinaryOp (Iff, phi1, phi2, _) ->
        (* t1 <=> t2 -> (t1 and t2) or (not t1 and not t2) *)
        dnf_of_aux ~process_pure exi_senv senv
        @@ mk_or
             (mk_and (nnf_of phi1) (nnf_of phi2))
             (mk_and (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2))
    | BinaryOp (Xor, phi1, phi2, _) ->
        (* t1 xor t2 -> (t1 and not t2) or (not t1 and t2) *)
        dnf_of_aux ~process_pure exi_senv senv
        @@ mk_or
             (mk_and (nnf_of phi1) (nnf_of @@ mk_neg phi2))
             (mk_and (nnf_of @@ mk_neg phi1) (nnf_of phi2))
    | Bind (_, _, _, _) -> assert false
    | LetRec (_, _, _) -> assert false
    | LetFormula (var, sort, def, body, info) ->
        let senv' = Map.Poly.set senv ~key:var ~data:sort in
        Set.Poly.map (dnf_of_aux ~process_pure exi_senv senv' body)
          ~f:(fun (ps, ns, phis) ->
            ( Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ps,
              Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ns,
              Set.Poly.singleton
              @@ insert_let_formula var sort def info
              @@ and_of @@ Set.to_list phis ))

  (* outputs the DNF formula represented by a list of clauses where a clause is represented by a triple [(ps,ns,phi')] consisting of
     [ps]: predicate variable applications,
     [ns] negated predicate variable applications, and
     [phi']: a pure formula *)
  (* assume that [phi] is in NNF and let-normalized *)
  (* assume that [phi1] and [phi2] in [phi1 = phi2] and [phi1 <> phi2] do not contain a predicate variable application *)
  let dnf_of ?(process_pure = false) exi_senv phi =
    phi
    |> dnf_of_aux ~process_pure exi_senv Map.Poly.empty
    |> Set.Poly.map ~f:(fun (ps, ns, phis) ->
           (ps, ns, and_of @@ Set.to_list phis))

  let rec cnf_of_aux ?(process_pure = false) exi_senv senv = function
    | Atom (Atom.True _, _) | UnaryOp (Not, Atom (Atom.False _, _), _) ->
        Set.Poly.empty
    | Atom (Atom.False _, _) | UnaryOp (Not, Atom (Atom.True _, _), _) ->
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | phi
      when (not process_pure)
           && Set.disjoint (fvs_of phi) (Map.key_set exi_senv) ->
        Set.Poly.singleton
          (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
    | Atom ((Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom), _)
      -> (
        let tvar = Ident.Tvar name in
        match (Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar) with
        | Some _, None ->
            Set.Poly.singleton
              (Set.Poly.singleton atom, Set.Poly.empty, Set.Poly.empty)
        | None, Some _ ->
            Set.Poly.singleton
              (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
        | _ -> failwith "cnf_of")
    | UnaryOp
        ( Not,
          Atom ((Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom), _),
          _ ) -> (
        let tvar = Ident.Tvar name in
        match (Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar) with
        | Some _, None ->
            Set.Poly.singleton
              (Set.Poly.empty, Set.Poly.singleton atom, Set.Poly.empty)
        | None, Some _ ->
            Set.Poly.singleton
              ( Set.Poly.empty,
                Set.Poly.empty,
                Set.Poly.singleton (mk_neg (mk_atom atom)) )
        | _ -> failwith "cnf_of")
    | Atom ((Atom.App (Predicate.Psym _, _, _) as atom), _) ->
        (* not reachable? *)
        Set.Poly.singleton
          (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
    | UnaryOp (Not, Atom ((Atom.App (Predicate.Psym _, _, _) as atom), _), _) ->
        (* not reachable? *)
        Set.Poly.singleton
          ( Set.Poly.empty,
            Set.Poly.empty,
            Set.Poly.singleton (mk_neg (mk_atom atom)) )
    | UnaryOp (Not, _, _) -> assert false
    | Atom (Atom.App (Predicate.Fixpoint _, _, _), _) ->
        failwith "not supported"
    | BinaryOp (And, phi1, phi2, _) ->
        let phis, cls =
          let cls1 = cnf_of_aux ~process_pure exi_senv senv phi1 in
          let cls2 = cnf_of_aux ~process_pure exi_senv senv phi2 in
          Set.union cls1 cls2
          |> Set.partition_map ~f:(fun (ps, ns, phis) ->
                 if
                   Set.is_empty ps && Set.is_empty ns
                   && Set.is_empty
                      @@ Set.inter (Map.key_set exi_senv)
                           (fvs_of @@ or_of @@ Set.to_list phis)
                 then First (or_of @@ Set.to_list phis)
                 else Second (ps, ns, phis))
        in
        if Set.is_empty phis then cls
        else if process_pure then
          Set.union cls
          @@ Set.Poly.map phis ~f:(fun phi ->
                 (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi))
        else
          Set.add cls
            ( Set.Poly.empty,
              Set.Poly.empty,
              Set.Poly.singleton @@ and_of @@ Set.to_list phis )
    | BinaryOp (Or, phi1, phi2, _) ->
        let cls1 = cnf_of_aux ~process_pure exi_senv senv phi1 in
        let cls2 = cnf_of_aux ~process_pure exi_senv senv phi2 in
        Set.cartesian_map cls1 cls2
          ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
            (Set.union ps1 ps2, Set.union ns1 ns2, Set.union phis1 phis2))
    | BinaryOp (Imply, phi1, phi2, _) ->
        cnf_of_aux ~process_pure exi_senv senv
        @@ mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2)
    | BinaryOp (Iff, phi1, phi2, _) ->
        (* t1 <=> t2 -> (not t1 or t2) and (t1 or not t2) *)
        cnf_of_aux ~process_pure exi_senv senv
        @@ mk_and
             (mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2))
             (mk_or (nnf_of phi1) (nnf_of @@ mk_neg phi2))
    | BinaryOp (Xor, phi1, phi2, _) ->
        (* t1 xor t2 -> (t1 or t2) and (not t1 or not t2) *)
        cnf_of_aux ~process_pure exi_senv senv
        @@ mk_and
             (mk_or (nnf_of phi1) (nnf_of phi2))
             (mk_or (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2))
    | Bind (binder, _, _, _) ->
        failwith
        @@ sprintf "[cnf_of_aux] %s not supported"
             (Formula.str_of_binder binder)
    | LetRec (_, _, _) -> assert false
    | LetFormula (var, sort, def, body, info) ->
        let senv' = Map.Poly.set senv ~key:var ~data:sort in
        Set.Poly.map (cnf_of_aux ~process_pure exi_senv senv' body)
          ~f:(fun (ps, ns, phis) ->
            ( Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ps,
              Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ns,
              Set.Poly.singleton
              @@ insert_let_formula var sort def info
              @@ or_of @@ Set.to_list phis ))

  (* outputs the CNF formula represented by a list of clauses where a clause is represented by a triple [(ps,ns,phi')] consisting of
     [ps]: predicate variable applications,
     [ns] negated predicate variable applications, and
     [phi']: a pure formula *)
  (* assume that [phi] is in NNF and let-normalized *)
  (* assume that [phi1] and [phi2] in [phi1 = phi2] and [phi1 <> phi2] do not contain a predicate variable application *)
  let cnf_of ?(process_pure = false) exi_senv =
    cnf_of_aux ~process_pure exi_senv Map.Poly.empty
    >> Set.Poly.map ~f:(fun (ps, ns, phis) ->
           (ps, ns, or_of @@ Set.to_list phis))

  let pnf_of f = uncurry mk_binds @@ split_quantifiers f

  (* assume that [phi] is in NNF and let-normalized *)
  let skolemize ~use_fn_pred ~only_impure =
    let rec aux senv fsenv = function
      | Atom (_, _) as phi ->
          (* assume that phi does not contain quantifiers *)
          (senv, fsenv, phi)
      | UnaryOp (unop, phi, _) ->
          let senv, fsenv, phi = aux senv fsenv phi in
          (senv, fsenv, mk_unop unop phi)
      | BinaryOp (binop, phi1, phi2, _) ->
          let senv, fsenv, phi1 = aux senv fsenv phi1 in
          let senv, fsenv, phi2 = aux senv fsenv phi2 in
          (senv, fsenv, mk_binop binop phi1 phi2)
      | Bind (Forall, uni_senv, phi, _) ->
          aux (Map.force_merge (Map.of_list_exn uni_senv) senv) fsenv phi
      | Bind (Exists, exi_senv, phi, _) ->
          if only_impure && (Set.is_empty @@ pvs_of phi) then
            let senv, fsenv, phi = aux senv fsenv phi in
            (senv, fsenv, mk_exists exi_senv phi)
          else
            let args = Map.Poly.to_alist senv in
            if use_fn_pred then
              let sub, senv, fsenv, fnpv_apps =
                List.fold ~init:(Map.Poly.empty, senv, fsenv, []) exi_senv
                  ~f:(fun
                      (sub, senv, fsenv, fnpv_apps) (Ident.Tvar name, sort) ->
                    let sk_tvar =
                      let prefix = Some ("#skolem_" ^ name) in
                      Ident.mk_fresh_tvar ~prefix ()
                    in
                    let sorts = List.map ~f:snd args @ [ sort ] in
                    let pvar =
                      let (Ident.Pvar new_name) = Ident.mk_fresh_pvar () in
                      Ident.(Pvar ("FN" ^ divide_flag ^ name ^ new_name))
                    in
                    let ret = Term.mk_var sk_tvar sort in
                    let fnpv_app =
                      Atom.mk_pvar_app pvar sorts
                      @@ Term.of_sort_env args @ [ ret ]
                    in
                    ( Map.Poly.add_exn sub ~key:(Ident.Tvar name) ~data:ret,
                      Map.Poly.add_exn senv ~key:sk_tvar ~data:sort,
                      Map.Poly.add_exn fsenv ~key:(Ident.pvar_to_tvar pvar)
                        ~data:(Sort.mk_fun @@ sorts @ [ T_bool.SBool ]),
                      Formula.mk_atom fnpv_app :: fnpv_apps ))
              in
              aux senv fsenv
                Formula.(mk_imply (and_of fnpv_apps) (subst sub phi))
            else
              let sub, fsenv =
                List.fold ~init:(Map.Poly.empty, fsenv) exi_senv
                  ~f:(fun (sub, fsenv) (Ident.Tvar name, sret) ->
                    let sk_tvar =
                      let prefix = Some ("#skolem_" ^ name) in
                      Ident.mk_fresh_tvar ~prefix ()
                    in
                    let sargs = List.map ~f:snd args in
                    let fapp =
                      Term.mk_fvar_app sk_tvar sargs sret
                      @@ Term.of_sort_env args
                    in
                    ( Map.Poly.add_exn sub ~key:(Ident.Tvar name) ~data:fapp,
                      Map.Poly.add_exn fsenv ~key:sk_tvar
                        ~data:(Sort.mk_fun (sargs @ [ sret ])) ))
              in
              aux senv fsenv (Formula.subst sub phi)
      | Bind (Random _, _, _, _) -> assert false (*ToDo*)
      | LetRec (_, _, _) -> assert false
      | LetFormula (var, sort, def, body, info) ->
          let senv, fsenv, body =
            aux (Map.Poly.add_exn ~key:var ~data:sort senv) fsenv body
          in
          (senv, fsenv, LetFormula (var, sort, def, body, info))
    in
    aux Map.Poly.empty Map.Poly.empty

  (** Observation *)

  let threshold = 10
  let enable = false
  let drop_let = true

  (* assume that [phi] is let-normalized *)
  let psym_pvar_apps_of ?(simplifier = Fn.id) phi =
    let pos, neg = atoms_of phi in
    let pos =
      Set.Poly.filter_map pos ~f:(fun atm ->
          try
            let atm =
              to_atom
              @@ (if drop_let then body_of_let else elim_let ~map:Map.Poly.empty)
              @@ simplifier @@ replace_let_body phi @@ mk_atom atm
            in
            let size =
              Atom.ast_size atm
              (*ToDo*)
            in
            (*print_endline @@ "size: " ^ string_of_int size;*)
            if enable && size >= threshold then None else Some atm
          with _ -> None)
    in
    let neg =
      Set.Poly.filter_map neg ~f:(fun atm ->
          try
            let atm =
              to_atom
              @@ (if drop_let then body_of_let else elim_let ~map:Map.Poly.empty)
              @@ simplifier @@ replace_let_body phi @@ mk_atom atm
            in
            let size =
              Atom.ast_size atm
              (*ToDo*)
            in
            (*print_endline @@ "size: " ^ string_of_int size;*)
            if enable && size >= threshold then None else Some atm
          with _ -> None)
    in
    let psyms, pos_pvars =
      Set.fold ~init:([], []) pos ~f:(fun (symapps, papps) atom ->
          if Atom.is_psym_app atom then (atom :: symapps, papps)
          else if Atom.is_pvar_app atom then (symapps, atom :: papps)
          else (symapps, papps))
    in
    let psyms, neg_pvars =
      Set.fold ~init:(psyms, []) neg ~f:(fun (symapps, papps) atom ->
          if Atom.is_psym_app atom then
            match Atom.negate atom with
            | None -> (symapps, papps)
            | Some neg_atom -> (neg_atom :: symapps, papps)
          else if Atom.is_pvar_app atom then (symapps, atom :: papps)
          else (symapps, papps))
    in
    (psyms, pos_pvars, neg_pvars)
end

and T_bool :
  (Type.T_boolType
    with type formula := Formula.t
     and type atom := Atom.t
     and type term := Term.t) = struct
  type fun_sym += Formula of Formula.t | IfThenElse
  type pred_sym += Eq | Neq
  type Sort.t += SBool

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

  let is_formula = function
    | Term.FunApp (Formula _, [], _) -> true
    | _ -> false

  let is_sbool = Term.sort_of >> Term.is_bool_sort

  (** Construction *)

  let of_formula ?(info = Dummy) = function
    | Formula.Atom (Atom.App (Predicate.Psym Eq, [ t1; t2 ], _), _)
      when is_true t2 ->
        t1
    | Formula.Atom (Atom.App (Predicate.Psym Eq, [ t1; t2 ], _), _)
      when is_true t1 ->
        t2
    | Formula.Atom (Atom.App (Predicate.Psym Neq, [ t1; t2 ], _), _)
      when is_false t2 ->
        t1
    | Formula.Atom (Atom.App (Predicate.Psym Neq, [ t1; t2 ], _), _)
      when is_false t1 ->
        t2
    | phi -> Term.mk_fsym_app (Formula phi) [] ~info

  let of_atom ?(info = Dummy) atom = of_formula (Formula.mk_atom atom) ~info
  let mk_true ?(info = Dummy) () = of_atom (Atom.mk_true ()) ~info
  let mk_false ?(info = Dummy) () = of_atom (Atom.mk_false ()) ~info
  let make ?(info = Dummy) b = if b then mk_true ~info () else mk_false ~info ()
  let mk_eq ?(info = Dummy) t1 t2 = Atom.mk_psym_app Eq [ t1; t2 ] ~info
  let mk_neq ?(info = Dummy) t1 t2 = Atom.mk_psym_app Neq [ t1; t2 ] ~info

  let mk_eqs ts =
    List.concat_mapi ts ~f:(fun i t ->
        List.foldi ts ~init:[] ~f:(fun i1 ret t1 ->
            if i1 <= i || Stdlib.(Term.sort_of t <> Term.sort_of t1) then ret
            else mk_eq t t1 :: ret))

  let mk_if_then_else ?(info = Dummy) cond then_ else_ =
    Term.mk_fsym_app IfThenElse [ cond; then_; else_ ] ~info

  let ifte ?(info = Dummy) phi = mk_if_then_else ~info (of_formula phi)

  let rec negate = function
    | Term.Var (x, s, _) ->
        assert (Term.is_bool_sort s);
        of_atom @@ Atom.of_neg_bool_var x
    | Term.FunApp (Formula phi, _, _) -> of_formula @@ Formula.negate phi
    | Term.FunApp (IfThenElse, [ t1; t2; t3 ], _) ->
        mk_if_then_else t1 (negate t2) (negate t3)
    | term ->
        if true then of_atom @@ Atom.of_neg_bool_term term
        else
          failwith
          @@ sprintf "[T_bool.negate] %s not supported"
          @@ Term.str_of term

  (** Destruction *)

  let let_bool = function
    | Term.FunApp (Formula (Formula.Atom (Atom.True _, _)), [], _) -> true
    | Term.FunApp (Formula (Formula.Atom (Atom.False _, _)), [], _) -> false
    | _ -> assert false

  let let_formula = function
    | Term.FunApp (Formula phi, [], _) -> phi
    | _ -> assert false
end

and T_int :
  (Type.T_intType with type iterm := Term.t and type iatom := Atom.t) = struct
  type fun_sym +=
    | Int of Z.t
    | Neg
    | Nop
    | Abs
    | Add
    | Sub
    | Mul
    | Div of Value.modulo
    | Rem of Value.modulo
    | Power

  type pred_sym += Leq | Geq | Lt | Gt | PDiv | NotPDiv
  type Sort.t += SInt | SRefInt | SUnrefInt

  (** Construction *)

  let mk_int ?(info = Dummy) n = Term.mk_fsym_app (Int n) [] ~info
  let from_int ?(info = Dummy) n = mk_int (Z.of_int n) ~info
  let zero ?(info = Dummy) () = mk_int Z.zero ~info
  let one ?(info = Dummy) () = mk_int Z.one ~info
  let hundred ?(info = Dummy) () = from_int 100 ~info
  let mk_add ?(info = Dummy) t1 t2 = Term.mk_fsym_app Add [ t1; t2 ] ~info
  let mk_sub ?(info = Dummy) t1 t2 = Term.mk_fsym_app Sub [ t1; t2 ] ~info
  let mk_mul ?(info = Dummy) t1 t2 = Term.mk_fsym_app Mul [ t1; t2 ] ~info
  let mk_div ?(info = Dummy) m t1 t2 = Term.mk_fsym_app (Div m) [ t1; t2 ] ~info
  let mk_rem ?(info = Dummy) m t1 t2 = Term.mk_fsym_app (Rem m) [ t1; t2 ] ~info
  let mk_neg ?(info = Dummy) t = Term.mk_fsym_app Neg [ t ] ~info

  (* let mk_neg ?(info=Dummy) t =
     mk_mul (mk_int (Z.neg Z.one) ~info) t ~info*)
  let mk_abs ?(info = Dummy) t = Term.mk_fsym_app Abs [ t ] ~info
  let mk_power ?(info = Dummy) t1 t2 = Term.mk_fsym_app Power [ t1; t2 ] ~info
  let mk_sum ?(info = Dummy) t ts = List.fold ~init:t ts ~f:(mk_add ~info)
  let mk_prod ?(info = Dummy) t ts = List.fold ~init:t ts ~f:(mk_mul ~info)
  let mk_leq ?(info = Dummy) t1 t2 = Atom.mk_psym_app Leq [ t1; t2 ] ~info
  let mk_geq ?(info = Dummy) t1 t2 = Atom.mk_psym_app Geq [ t1; t2 ] ~info
  let mk_lt ?(info = Dummy) t1 t2 = Atom.mk_psym_app Lt [ t1; t2 ] ~info
  let mk_gt ?(info = Dummy) t1 t2 = Atom.mk_psym_app Gt [ t1; t2 ] ~info
  let mk_pdiv ?(info = Dummy) t1 t2 = Atom.mk_psym_app PDiv [ t1; t2 ] ~info

  let mk_not_pdiv ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app NotPDiv [ t1; t2 ] ~info

  let mk_min ?(info = Dummy) t1 t2 =
    T_bool.ifte (Formula.mk_atom @@ mk_leq t1 t2) t1 t2 ~info

  let mk_max ?(info = Dummy) t1 t2 =
    T_bool.ifte (Formula.mk_atom @@ mk_leq t1 t2) t2 t1 ~info

  (*let abs t = T_bool.ifte (Formula.geq t (zero ())) t (mk_neg t)*)
  let l1_norm ts = mk_sum (zero ()) (List.map ~f:mk_abs ts)
  let l2_norm_sq ts = mk_sum (zero ()) (List.map ~f:(fun t -> mk_mul t t) ts)

  (** Destruction *)

  let let_int = function Term.FunApp (Int n, [], _) -> n | _ -> assert false

  let let_add = function
    | Term.FunApp (Add, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_sub = function
    | Term.FunApp (Sub, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_mul = function
    | Term.FunApp (Mul, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_div = function
    | Term.FunApp (Div m, [ t1; t2 ], info) -> (m, t1, t2, info)
    | _ -> assert false

  let let_rem = function
    | Term.FunApp (Rem m, [ t1; t2 ], info) -> (m, t1, t2, info)
    | _ -> assert false

  let let_neg = function
    | Term.FunApp (Neg, [ t ], info) -> (t, info)
    | _ -> assert false

  let let_abs = function
    | Term.FunApp (Abs, [ t ], info) -> (t, info)
    | _ -> assert false

  let let_power = function
    | Term.FunApp (Power, [ phi1; phi2 ], info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_leq = function
    | Atom.App (Predicate.Psym Leq, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_geq = function
    | Atom.App (Predicate.Psym Geq, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_lt = function
    | Atom.App (Predicate.Psym Lt, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_gt = function
    | Atom.App (Predicate.Psym Gt, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_pdiv = function
    | Atom.App (Predicate.Psym PDiv, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_not_pdiv = function
    | Atom.App (Predicate.Psym NotPDiv, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  (** Observation *)

  let is_sint t = Term.is_int_sort @@ Term.sort_of t
  let is_int = function Term.FunApp (Int _, [], _) -> true | _ -> false
  let is_add = function Term.FunApp (Add, _, _) -> true | _ -> false
  let is_sub = function Term.FunApp (Sub, _, _) -> true | _ -> false
  let is_mul = function Term.FunApp (Mul, _, _) -> true | _ -> false
  let is_div = function Term.FunApp (Div _, _, _) -> true | _ -> false
  let is_rem = function Term.FunApp (Rem _, _, _) -> true | _ -> false
  let is_neg = function Term.FunApp (Neg, _, _) -> true | _ -> false
  let is_abs = function Term.FunApp (Abs, _, _) -> true | _ -> false
  let is_power = function Term.FunApp (Power, _, _) -> true | _ -> false

  let is_zero = function
    | Term.FunApp (Int i, _, _) when Z.Compare.(i = Z.zero) -> true
    | _ -> false

  let is_unit = function
    | Term.FunApp (Int i, _, _) when Z.Compare.(i = Z.one) -> true
    | _ -> false

  let is_minus_one = function
    | Term.FunApp (Int i, _, _) when Z.Compare.(i = Z.minus_one) -> true
    | _ -> false

  let psym_of_atom = function
    | Atom.App (Predicate.Psym sym, _, _) -> sym
    | _ -> assert false

  let is_leq atom = Stdlib.(Leq = psym_of_atom atom)
  let is_geq atom = Stdlib.(Geq = psym_of_atom atom)
  let is_lt atom = Stdlib.(Lt = psym_of_atom atom)
  let is_gt atom = Stdlib.(Gt = psym_of_atom atom)
  let is_pdiv atom = Stdlib.(PDiv = psym_of_atom atom)
  let is_not_pdiv atom = Stdlib.(NotPDiv = psym_of_atom atom)
end

and T_real :
  (Type.T_realType with type rterm := Term.t and type ratom := Atom.t) = struct
  type fun_sym +=
    | Real of Q.t
    | Alge of int
    | RNeg
    | RAbs
    | RAdd
    | RSub
    | RMul
    | RDiv
    | RPower

  type pred_sym += RLeq | RGeq | RLt | RGt
  type Sort.t += SReal

  (** Construction *)

  let mk_real ?(info = Dummy) f = Term.mk_fsym_app (Real f) [] ~info
  let mk_alge ?(info = Dummy) t n = Term.mk_fsym_app (Alge n) [ t ] ~info
  let rzero ?(info = Dummy) () = mk_real Q.zero ~info
  let rone ?(info = Dummy) () = mk_real Q.one ~info
  let mk_radd ?(info = Dummy) t1 t2 = Term.mk_fsym_app RAdd [ t1; t2 ] ~info
  let mk_rsub ?(info = Dummy) t1 t2 = Term.mk_fsym_app RSub [ t1; t2 ] ~info
  let mk_rmul ?(info = Dummy) t1 t2 = Term.mk_fsym_app RMul [ t1; t2 ] ~info
  let mk_rdiv ?(info = Dummy) t1 t2 = Term.mk_fsym_app RDiv [ t1; t2 ] ~info
  let mk_rneg ?(info = Dummy) t = Term.mk_fsym_app RNeg [ t ] ~info

  (* let mk_neg ?(info=Dummy) t =
     mk_mul (mk_int (Z.neg Z.one) ~info) t ~info*)
  let mk_rabs ?(info = Dummy) t = Term.mk_fsym_app RAbs [ t ] ~info
  let mk_rpower ?(info = Dummy) t1 t2 = Term.mk_fsym_app RPower [ t1; t2 ] ~info
  let mk_rsum ?(info = Dummy) t ts = List.fold ~init:t ts ~f:(mk_radd ~info)
  let mk_rprod ?(info = Dummy) t ts = List.fold ~init:t ts ~f:(mk_rmul ~info)
  let mk_rleq ?(info = Dummy) t1 t2 = Atom.mk_psym_app RLeq [ t1; t2 ] ~info
  let mk_rgeq ?(info = Dummy) t1 t2 = Atom.mk_psym_app RGeq [ t1; t2 ] ~info
  let mk_rlt ?(info = Dummy) t1 t2 = Atom.mk_psym_app RLt [ t1; t2 ] ~info
  let mk_rgt ?(info = Dummy) t1 t2 = Atom.mk_psym_app RGt [ t1; t2 ] ~info

  let mk_rmin ?(info = Dummy) t1 t2 =
    T_bool.ifte (Formula.mk_atom @@ mk_rleq t1 t2) t1 t2 ~info

  let mk_rmax ?(info = Dummy) t1 t2 =
    T_bool.ifte (Formula.mk_atom @@ mk_rleq t1 t2) t2 t1 ~info

  let l1_norm ts = mk_rsum (rzero ()) (List.map ~f:mk_rabs ts)
  let l2_norm_sq ts = mk_rsum (rzero ()) (List.map ~f:(fun t -> mk_rmul t t) ts)

  (** Destruction *)

  let let_real = function
    | Term.FunApp (Real f, [], _) -> f
    | t -> failwith @@ sprintf "%s is not real" @@ Term.str_of t

  let let_alge = function
    | Term.FunApp (Alge n, [ t ], _) -> (t, n)
    | _ -> assert false

  let let_radd = function
    | Term.FunApp (RAdd, [ phi1; phi2 ], info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_rsub = function
    | Term.FunApp (RSub, [ phi1; phi2 ], info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_rmul = function
    | Term.FunApp (RMul, [ phi1; phi2 ], info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_rdiv = function
    | Term.FunApp (RDiv, [ phi1; phi2 ], info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_rneg = function
    | Term.FunApp (RNeg, [ t ], info) -> (t, info)
    | _ -> assert false

  let let_rabs = function
    | Term.FunApp (RAbs, [ t ], info) -> (t, info)
    | _ -> assert false

  let let_rpower = function
    | Term.FunApp (RPower, [ phi1; phi2 ], info) -> (phi1, phi2, info)
    | _ -> assert false

  let let_rleq = function
    | Atom.App (Predicate.Psym RLeq, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_rgeq = function
    | Atom.App (Predicate.Psym RGeq, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_rlt = function
    | Atom.App (Predicate.Psym RLt, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_rgt = function
    | Atom.App (Predicate.Psym RGt, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  (** Observation *)

  let is_sreal t = Term.is_real_sort @@ Term.sort_of t
  let is_real = function Term.FunApp (Real _, [], _) -> true | _ -> false
  let is_alge = function Term.FunApp (Alge _, [ _ ], _) -> true | _ -> false
  let is_radd = function Term.FunApp (RAdd, _, _) -> true | _ -> false
  let is_rsub = function Term.FunApp (RSub, _, _) -> true | _ -> false
  let is_rmul = function Term.FunApp (RMul, _, _) -> true | _ -> false
  let is_rdiv = function Term.FunApp (RDiv, _, _) -> true | _ -> false
  let is_rneg = function Term.FunApp (RNeg, _, _) -> true | _ -> false
  let is_rabs = function Term.FunApp (RAbs, _, _) -> true | _ -> false
  let is_rpower = function Term.FunApp (RPower, _, _) -> true | _ -> false

  let is_rzero = function
    | Term.FunApp (Real r, _, _) when Q.(r = zero) -> true
    | _ -> false

  let is_runit = function
    | Term.FunApp (Real r, _, _) when Q.(r = one) -> true
    | _ -> false

  let is_rminus_one = function
    | Term.FunApp (Real r, _, _) when Q.(r = minus_one) -> true
    | _ -> false

  let psym_of_atom = function
    | Atom.App (Predicate.Psym sym, _, _) -> sym
    | _ -> assert false

  let is_rleq atom = Stdlib.(RLeq = psym_of_atom atom)
  let is_rgeq atom = Stdlib.(RGeq = psym_of_atom atom)
  let is_rlt atom = Stdlib.(RLt = psym_of_atom atom)
  let is_rgt atom = Stdlib.(RGt = psym_of_atom atom)
end

and T_bv :
  (Type.T_bvType with type bvterm := Term.t and type bvatom := Atom.t) = struct
  type size = int (* bits *) option
  type signed = bool (* signed/unsigned *) option

  type fun_sym +=
    | BVNum of size * Z.t
    | BVNot of size
    | BVAnd of size
    | BVOr of size
    | BVXor of size
    | BVNand of size
    | BVNor of size
    | BVXnor of size
    | BVNeg of size
    | BVAdd of size
    | BVSub of size
    | BVMul of size
    | BVDiv of size * signed
    | BVRem of size * signed
    | BVSMod of size
    | BVSHL of size
    | BVLSHR of size
    | BVASHR of size
    | BVEXTRACT of size * int * int
    | BVSEXT of size * int
    | BVZEXT of size * int
    | BVCONCAT of size * size

  type pred_sym +=
    | BVLeq of size * signed
    | BVGeq of size * signed
    | BVLt of size * signed
    | BVGt of size * signed

  type Sort.t += SBV of size

  (** Observation *)

  let bits_of = function None -> 32 (*ToDo*) | Some bits -> bits

  (** Construction *)

  let mk_bvnum ?(info = Dummy) ~size n =
    Term.mk_fsym_app (BVNum (size, int2bv (bits_of size) n)) [] ~info

  let mk_bvnot ?(info = Dummy) ~size t =
    Term.mk_fsym_app (BVNot size) [ t ] ~info

  let mk_bvand ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVAnd size) [ t1; t2 ] ~info

  let mk_bvor ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVOr size) [ t1; t2 ] ~info

  let mk_bvxor ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVXor size) [ t1; t2 ] ~info

  let mk_bvnand ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVNand size) [ t1; t2 ] ~info

  let mk_bvnor ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVNor size) [ t1; t2 ] ~info

  let mk_bvxnor ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVXnor size) [ t1; t2 ] ~info

  let mk_bvneg ?(info = Dummy) ~size t =
    Term.mk_fsym_app (BVNeg size) [ t ] ~info

  let mk_bvadd ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVAdd size) [ t1; t2 ] ~info

  let mk_bvsub ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVSub size) [ t1; t2 ] ~info

  let mk_bvmul ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVMul size) [ t1; t2 ] ~info

  let mk_bvdiv ?(info = Dummy) ~size ~signed t1 t2 =
    Term.mk_fsym_app (BVDiv (size, signed)) [ t1; t2 ] ~info

  let mk_bvrem ?(info = Dummy) ~size ~signed t1 t2 =
    Term.mk_fsym_app (BVRem (size, signed)) [ t1; t2 ] ~info

  let mk_bvsmod ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVSMod size) [ t1; t2 ] ~info

  let mk_bvshl ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVSHL size) [ t1; t2 ] ~info

  let mk_bvlshr ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVLSHR size) [ t1; t2 ] ~info

  let mk_bvashr ?(info = Dummy) ~size t1 t2 =
    Term.mk_fsym_app (BVASHR size) [ t1; t2 ] ~info

  let mk_bvextract ?(info = Dummy) ~size h l t1 =
    Term.mk_fsym_app (BVEXTRACT (size, h, l)) [ t1 ] ~info

  let mk_bvsext ?(info = Dummy) ~size ext t1 =
    Term.mk_fsym_app (BVSEXT (size, ext)) [ t1 ] ~info

  let mk_bvzext ?(info = Dummy) ~size ext t1 =
    Term.mk_fsym_app (BVZEXT (size, ext)) [ t1 ] ~info

  let mk_bvconcat ?(info = Dummy) ~size1 ~size2 t1 t2 =
    Term.mk_fsym_app (BVCONCAT (size1, size2)) [ t1; t2 ] ~info

  let mk_bvleq ?(info = Dummy) ~size ~signed t1 t2 =
    Atom.mk_psym_app (BVLeq (size, signed)) [ t1; t2 ] ~info

  let mk_bvgeq ?(info = Dummy) ~size ~signed t1 t2 =
    Atom.mk_psym_app (BVGeq (size, signed)) [ t1; t2 ] ~info

  let mk_bvlt ?(info = Dummy) ~size ~signed t1 t2 =
    Atom.mk_psym_app (BVLt (size, signed)) [ t1; t2 ] ~info

  let mk_bvgt ?(info = Dummy) ~size ~signed t1 t2 =
    Atom.mk_psym_app (BVGt (size, signed)) [ t1; t2 ] ~info

  (** Observation *)

  let bvzero ?(info = Dummy) ~size () = mk_bvnum ~info ~size Z.zero
  let bvone ?(info = Dummy) ~size () = mk_bvnum ~info ~size Z.one

  let mk_bvsum ?(info = Dummy) ~size t ts =
    List.fold ~init:t ts ~f:(mk_bvadd ~info ~size)

  (** Destruction *)

  let let_bv = function
    | Term.FunApp (BVNum (size, n), [], _) -> (size, n)
    | _ -> assert false

  let let_bvnot = function
    | Term.FunApp (BVNot size, [ t1 ], info) -> (size, t1, info)
    | _ -> assert false

  let let_bvand = function
    | Term.FunApp (BVAnd size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvor = function
    | Term.FunApp (BVOr size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvxor = function
    | Term.FunApp (BVXor size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvnand = function
    | Term.FunApp (BVNand size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvnor = function
    | Term.FunApp (BVNor size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvxnor = function
    | Term.FunApp (BVXnor size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvneg = function
    | Term.FunApp (BVNeg size, [ t1 ], info) -> (size, t1, info)
    | _ -> assert false

  let let_bvadd = function
    | Term.FunApp (BVAdd size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvsub = function
    | Term.FunApp (BVSub size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvmul = function
    | Term.FunApp (BVMul size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvdiv = function
    | Term.FunApp (BVDiv (size, signed), [ t1; t2 ], info) ->
        (size, signed, t1, t2, info)
    | _ -> assert false

  let let_bvrem = function
    | Term.FunApp (BVRem (size, signed), [ t1; t2 ], info) ->
        (size, signed, t1, t2, info)
    | _ -> assert false

  let let_bvsmod = function
    | Term.FunApp (BVSMod size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvshl = function
    | Term.FunApp (BVSHL size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvlshr = function
    | Term.FunApp (BVLSHR size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvashr = function
    | Term.FunApp (BVASHR size, [ t1; t2 ], info) -> (size, t1, t2, info)
    | _ -> assert false

  let let_bvextract = function
    | Term.FunApp (BVEXTRACT (size, h, l), [ t1 ], info) ->
        (size, h, l, t1, info)
    | _ -> assert false

  let let_bvsext = function
    | Term.FunApp (BVSEXT (size, ext), [ t1 ], info) -> (size, ext, t1, info)
    | _ -> assert false

  let let_bvzext = function
    | Term.FunApp (BVZEXT (size, ext), [ t1 ], info) -> (size, ext, t1, info)
    | _ -> assert false

  let let_bvconcat = function
    | Term.FunApp (BVCONCAT (size1, size2), [ t1; t2 ], info) ->
        (size1, size2, t1, t2, info)
    | _ -> assert false

  let let_bvleq = function
    | Atom.App (Predicate.Psym (BVLeq (size, signed)), [ t1; t2 ], info) ->
        (size, signed, t1, t2, info)
    | _ -> assert false

  let let_bvgeq = function
    | Atom.App (Predicate.Psym (BVGeq (size, signed)), [ t1; t2 ], info) ->
        (size, signed, t1, t2, info)
    | _ -> assert false

  let let_bvlt = function
    | Atom.App (Predicate.Psym (BVLt (size, signed)), [ t1; t2 ], info) ->
        (size, signed, t1, t2, info)
    | _ -> assert false

  let let_bvgt = function
    | Atom.App (Predicate.Psym (BVGt (size, signed)), [ t1; t2 ], info) ->
        (size, signed, t1, t2, info)
    | _ -> assert false

  (** Observation *)

  let signed_of = function None -> true (*ToDo*) | Some signed -> signed

  let is_bv_fsym = function
    | BVNum _ | BVNot _ | BVAnd _ | BVOr _ | BVXor _ | BVNand _ | BVNor _
    | BVXnor _ | BVNeg _ | BVAdd _ | BVSub _ | BVMul _ | BVDiv _ | BVRem _
    | BVSMod _ | BVSHL _ | BVLSHR _ | BVASHR _ | BVEXTRACT _ | BVSEXT _
    | BVZEXT _ | BVCONCAT _ ->
        true
    | _ -> false

  let is_bv_psym = function
    | BVLeq _ | BVGeq _ | BVLt _ | BVGt _ -> true
    | _ -> false

  let is_sbv t = Term.is_bv_sort @@ Term.sort_of t
  let is_bv = function Term.FunApp (BVNum _, [], _) -> true | _ -> false

  let is_bvzero = function
    | Term.FunApp (BVNum (_size, i), _, _) when Z.Compare.(i = Z.zero) -> true
    | _ -> false

  let is_bvunit = function
    | Term.FunApp (BVNum (_size, i), _, _) when Z.Compare.(i = Z.one) -> true
    | _ -> false

  let is_bvnot = function Term.FunApp (BVNot _, _, _) -> true | _ -> false
  let is_bvand = function Term.FunApp (BVAnd _, _, _) -> true | _ -> false
  let is_bvor = function Term.FunApp (BVOr _, _, _) -> true | _ -> false
  let is_bvxor = function Term.FunApp (BVXor _, _, _) -> true | _ -> false
  let is_bvnand = function Term.FunApp (BVNand _, _, _) -> true | _ -> false
  let is_bvnor = function Term.FunApp (BVNor _, _, _) -> true | _ -> false
  let is_bvxnor = function Term.FunApp (BVXnor _, _, _) -> true | _ -> false
  let is_bvneg = function Term.FunApp (BVNeg _, _, _) -> true | _ -> false
  let is_bvadd = function Term.FunApp (BVAdd _, _, _) -> true | _ -> false
  let is_bvsub = function Term.FunApp (BVSub _, _, _) -> true | _ -> false
  let is_bvmul = function Term.FunApp (BVMul _, _, _) -> true | _ -> false
  let is_bvdiv = function Term.FunApp (BVDiv _, _, _) -> true | _ -> false
  let is_bvrem = function Term.FunApp (BVRem _, _, _) -> true | _ -> false
  let is_bvsmod = function Term.FunApp (BVSMod _, _, _) -> true | _ -> false
  let is_bvshl = function Term.FunApp (BVSHL _, _, _) -> true | _ -> false
  let is_bvlshr = function Term.FunApp (BVLSHR _, _, _) -> true | _ -> false
  let is_bvashr = function Term.FunApp (BVASHR _, _, _) -> true | _ -> false

  let is_bvextract = function
    | Term.FunApp (BVEXTRACT _, _, _) -> true
    | _ -> false

  let is_bvsext = function Term.FunApp (BVSEXT _, _, _) -> true | _ -> false
  let is_bvzext = function Term.FunApp (BVZEXT _, _, _) -> true | _ -> false

  let is_bvconcat = function
    | Term.FunApp (BVCONCAT _, _, _) -> true
    | _ -> false

  let is_bvleq = function
    | Atom.App (Predicate.Psym (BVLeq _), _, _) -> true
    | _ -> false

  let is_bvgeq = function
    | Atom.App (Predicate.Psym (BVGeq _), _, _) -> true
    | _ -> false

  let is_bvlt = function
    | Atom.App (Predicate.Psym (BVLt _), _, _) -> true
    | _ -> false

  let is_bvgt = function
    | Atom.App (Predicate.Psym (BVGt _), _, _) -> true
    | _ -> false

  (** Printing *)

  let str_of_size = function None -> "?" | Some bits -> sprintf "%d" bits

  let str_of_signed = function
    | None -> "?"
    | Some signed -> if signed then "s" else "u"

  (** Size manipulation *)

  let eq_size size1 size2 =
    (* Stdlib.(bits_of size1 = bits_of size2) *)
    match (size1, size2) with
    | Some s1, Some s2 -> Stdlib.(s1 = s2)
    | _ -> true (*ToDo*)

  let merge_size size1 size2 =
    match (size1, size2) with
    | Some s1, Some s2 ->
        assert (s1 = s2);
        Some s1
    | _ -> None

  let geq_size size1 size2 =
    (* Stdlib.(bits_of size1 >= bits_of size2) *)
    match (size1, size2) with
    | Some s1, Some s2 -> Stdlib.(s1 >= s2)
    | _ -> true (*ToDo*)

  let ext_size size ext =
    match size with Some s -> Some (s + ext) | None -> None

  let add_size size1 size2 =
    match (size1, size2) with Some s1, Some s2 -> Some (s1 + s2) | _ -> None

  let max_size size1 size2 =
    match (size1, size2) with
    | None, _ -> size2 (* ToDo *)
    | _, None -> size1 (* ToDo *)
    | Some s1, Some s2 -> Some (Stdlib.max s1 s2)

  let max_size_list = function
    | [] -> None
    | size :: sizes -> List.fold ~init:size sizes ~f:max_size
end

and T_irb :
  (Type.T_irbType
    with type iterm := Term.t
     and type iatom := Atom.t
     and type rterm := Term.t
     and type ratom := Atom.t
     and type bvterm := Term.t
     and type bvatom := Atom.t
     and type term := Term.t
     and type atom := Atom.t
     and type formula := Formula.t) = struct
  include T_int
  include T_real
  include T_bv

  type fun_sym +=
    | IntToReal
    | RealToInt
    | IntToBV of size
    | BVToInt of size * signed

  type pred_sym += IsInt

  (** Construction *)

  let mk_int_to_real ?(info = Dummy) t = Term.mk_fsym_app IntToReal [ t ] ~info
  let mk_real_to_int ?(info = Dummy) t = Term.mk_fsym_app RealToInt [ t ] ~info

  let mk_int_to_bv ?(info = Dummy) ~size t =
    Term.mk_fsym_app (IntToBV size) [ t ] ~info

  let mk_bv_to_int ?(info = Dummy) ~size ~signed t =
    Term.mk_fsym_app (BVToInt (size, signed)) [ t ] ~info

  let mk_is_int ?(info = Dummy) t = Atom.mk_psym_app IsInt [ t ] ~info

  let to_int_if_rb t =
    match Term.sort_of t with
    | T_real.SReal -> mk_real_to_int t
    | T_bv.SBV size -> mk_bv_to_int ~size ~signed:(Some true (*ToDo*)) t
    | _ -> t

  let to_real_if_int t = if T_real.is_sreal t then t else mk_int_to_real t

  (** Destruction *)

  let let_int_to_real = function
    | Term.FunApp (IntToReal, [ t ], info) -> (t, info)
    | _ -> assert false

  let let_real_to_int = function
    | Term.FunApp (RealToInt, [ t ], info) -> (t, info)
    | _ -> assert false

  let let_int_to_bv = function
    | Term.FunApp (IntToBV size, [ t ], info) -> (size, t, info)
    | _ -> assert false

  let let_bv_to_int = function
    | Term.FunApp (BVToInt (size, signed), [ t ], info) ->
        (size, signed, t, info)
    | _ -> assert false

  let let_is_int = function
    | Atom.App (Predicate.Psym IsInt, [ t ], info) -> (t, info)
    | _ -> assert false

  (** Observation *)

  let is_sint_sreal t =
    let s = Term.sort_of t in
    Term.is_int_sort s || Term.is_real_sort s

  let is_sirb t = Term.is_irb_sort @@ Term.sort_of t

  let is_int_to_real = function
    | Term.FunApp (IntToReal, _, _) -> true
    | _ -> false

  let is_real_to_int = function
    | Term.FunApp (RealToInt, _, _) -> true
    | _ -> false

  let is_int_to_bv = function
    | Term.FunApp (IntToBV _, _, _) -> true
    | _ -> false

  let is_bv_to_int = function
    | Term.FunApp (BVToInt _, _, _) -> true
    | _ -> false

  let psym_of_atom = function
    | Atom.App (Predicate.Psym sym, _, _) -> sym
    | _ -> assert false

  let is_is_int atom = Stdlib.(IsInt = psym_of_atom atom)

  let origin_of sorts =
    List.map sorts ~f:(function
      | T_bool.SBool -> T_bool.mk_false ()
      | T_int.SInt -> T_int.zero ()
      | T_real.SReal -> T_real.rzero ()
      | T_bv.SBV size -> T_bv.bvzero ~size ()
      | _ -> failwith "not supported")

  let zero_of = function
    | T_int.SInt -> T_int.zero ()
    | T_real.SReal -> T_real.rzero ()
    | T_bv.SBV size -> T_bv.bvzero ~size ()
    | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

  let mul = function
    | T_int.SInt -> T_int.mk_mul
    | T_real.SReal -> T_real.mk_rmul
    | T_bv.SBV size -> T_bv.mk_bvmul ~size
    | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

  let sum = function
    | T_int.SInt -> T_int.mk_sum
    | T_real.SReal -> T_real.mk_rsum
    | T_bv.SBV size -> T_bv.mk_bvsum ~size
    | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

  let geq = function
    | T_int.SInt -> T_int.mk_geq
    | T_real.SReal -> T_real.mk_rgeq
    | T_bv.SBV size -> T_bv.mk_bvgeq ~size ~signed:(Some true (*ToDo*))
    | sort -> failwith ("not supported: " ^ Term.str_of_sort sort)

  let cast = function
    | T_int.SInt, T_int.SInt | T_real.SReal, T_real.SReal -> Fn.id
    | T_bv.SBV size1, T_bv.SBV size2 ->
        if T_bv.eq_size size1 size2 then Fn.id
        else if T_bv.geq_size size2 size1 then fun t ->
          T_bv.mk_bvsext ~size:size1 (T_bv.bits_of size2 - T_bv.bits_of size1) t
        else
          failwith @@ "not supported: "
          ^ Term.str_of_sort (T_bv.SBV size1)
          ^ ", "
          ^ Term.str_of_sort (T_bv.SBV size2)
    | T_int.SInt, T_real.SReal -> fun t -> mk_int_to_real t
    | T_int.SInt, T_bv.SBV size -> fun t -> mk_int_to_bv ~size t
    | T_real.SReal, T_int.SInt -> fun t -> mk_real_to_int t
    | T_real.SReal, T_bv.SBV size ->
        fun t -> mk_int_to_bv ~size @@ mk_real_to_int t
    | T_bv.SBV size, T_int.SInt ->
        fun t -> mk_bv_to_int ~size ~signed:(Some true (*ToDo*)) t
    | T_bv.SBV size, T_real.SReal ->
        fun t ->
          mk_int_to_real @@ mk_bv_to_int ~size ~signed:(Some true (*ToDo*)) t
    | sort1, sort2 ->
        failwith
        @@ sprintf "not supported: %s, %s" (Term.str_of_sort sort1)
             (Term.str_of_sort sort2)

  let sum_of sort term ts =
    let coeffs, terms =
      List.unzip
      @@ List.map ts ~f:(fun (t, s) ->
             let coeff = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
             (coeff, cast (s, sort) (mul s (cast (T_int.SInt, s) coeff) t)))
    in
    (coeffs, sum sort term terms)

  let ineq_of sort ts =
    let negb = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
    let term = cast (T_int.SInt, sort) negb in
    let coeffs, term' =
      match sort with
      | T_bv.SBV size ->
          let coeffs, terms =
            List.unzip
            @@ List.map ts ~f:(fun (t, s) ->
                   let coeff =
                     Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt
                   in
                   let t = cast (s, sort) t in
                   ( coeff,
                     T_bool.ifte
                       (Formula.gt coeff (T_int.zero ()))
                       t
                       (T_bool.ifte
                          (Formula.lt coeff (T_int.zero ()))
                          (T_bv.mk_bvneg ~size t) (T_bv.bvzero ~size ())) ))
          in
          (coeffs, sum sort term terms)
      | _ -> sum_of sort term ts
    in
    ([ (coeffs, negb) ], Formula.mk_atom @@ geq sort term' (zero_of sort))

  let eq_of sort ts =
    let negb = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
    let term = cast (T_int.SInt, sort) negb in
    let coeffs, term' =
      match sort with
      | T_bv.SBV size ->
          let coeffs, terms =
            List.unzip
            @@ List.map ts ~f:(fun (t, s) ->
                   let coeff =
                     Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt
                   in
                   let t = cast (s, sort) t in
                   ( coeff,
                     T_bool.ifte
                       (Formula.gt coeff (T_int.zero ()))
                       t
                       (T_bool.ifte
                          (Formula.lt coeff (T_int.zero ()))
                          (T_bv.mk_bvneg ~size t) (T_bv.bvzero ~size ())) ))
          in
          (coeffs, sum sort term terms)
      | _ -> sum_of sort term ts
    in
    ([ (coeffs, negb) ], Formula.mk_atom @@ T_bool.mk_eq term' (zero_of sort))

  (* Auxliary functions for templates *)

  let bool_terms_of =
    List.filter ~f:(function _, T_bool.SBool -> true | _, _ -> false)

  let num_terms_of =
    List.filter ~f:(function
      | _, T_int.SInt | _, T_real.SReal | _, T_bv.SBV _ -> true
      | _, _ -> false)

  let num_sort_of terms =
    let sorts = Set.Poly.of_list @@ List.map ~f:snd terms in
    if Set.mem sorts T_real.SReal then T_real.SReal
    else if Set.mem sorts T_int.SInt then T_int.SInt
    else
      match
        Set.to_list
        @@ Set.Poly.filter_map sorts ~f:(function
             | T_bv.SBV size -> Some size
             | _ -> None)
      with
      | [] -> T_int.SInt (* failwith "no int/real/bv term" *)
      | sizes -> T_bv.SBV (T_bv.max_size_list sizes)

  let br_bools_of f ts =
    let bool_ts = bool_terms_of ts in
    let num_ts = num_terms_of ts in
    let rec aux = function
      | [] -> f num_ts
      | (t, _) :: ts ->
          let params1, tmpl1 = aux ts in
          let params2, tmpl2 = aux ts in
          ( params1 @ params2,
            Formula.or_of
              [
                Formula.and_of [ Formula.of_bool_term t; tmpl1 ];
                Formula.and_of
                  [ Formula.mk_neg @@ Formula.of_bool_term t; tmpl2 ];
              ] )
    in
    aux bool_ts
end

and T_num : (Type.T_numType with type term := Term.t and type atom := Atom.t) =
struct
  type fun_sym +=
    | Value of string * Ident.svar
    | NNeg of Ident.svar
    | NSEXT of int option * Ident.svar * int * Ident.svar
    | NAdd of Ident.svar
    | NSub of Ident.svar
    | NMul of Ident.svar
    | NDiv of Ident.svar * Value.modulo
    | NRem of Ident.svar * Value.modulo
    | NPower of Ident.svar

  type pred_sym +=
    | NLeq of Ident.svar
    | NGeq of Ident.svar
    | NLt of Ident.svar
    | NGt of Ident.svar

  exception NotValue

  (** Construction *)

  let mk_value ?(info = Dummy) num_str =
    if
      String.is_prefix num_str ~prefix:"e"
      || String.is_prefix num_str ~prefix:"E"
      || String.is_prefix num_str ~prefix:"_"
    then raise NotValue
    else
      try
        let n = Z.of_string num_str in
        Term.mk_fsym_app
          (Value (Z.to_string n, Ident.mk_fresh_svar ()))
          [] ~info
      with _ -> (
        try
          let r = Q.of_string num_str in
          Term.mk_fsym_app
            (Value (Q.to_string r, Ident.mk_fresh_svar ()))
            [] ~info
        with _ -> (
          try
            let f = Q.of_float @@ float_of_string num_str in
            Term.mk_fsym_app
              (Value (Q.to_string f, Ident.mk_fresh_svar ()))
              [] ~info
          with _ -> raise NotValue))

  let mk_neg_value ?(info = Dummy) num_str =
    if
      String.is_prefix num_str ~prefix:"e"
      || String.is_prefix num_str ~prefix:"E"
      || String.is_prefix num_str ~prefix:"_"
    then raise NotValue
    else
      let z =
        try
          let n = Z.of_string num_str in
          Z.to_string (Z.neg n)
        with _ -> (
          try
            let r = Q.of_string num_str in
            Q.to_string (Q.neg r)
          with _ -> (
            try
              let r = Q.of_float @@ float_of_string num_str in
              Q.to_string (Q.neg r)
            with _ -> raise NotValue))
      in
      Term.mk_fsym_app (Value (z, Ident.mk_fresh_svar ())) [] ~info

  let mk_nneg ?(info = Dummy) t1 =
    Term.mk_fsym_app (NNeg (Ident.mk_fresh_svar ())) [ t1 ] ~info

  let mk_nsext ?(info = Dummy) ~size ext t1 =
    Term.mk_fsym_app
      (NSEXT (size, Ident.mk_fresh_svar (), ext, Ident.mk_fresh_svar ()))
      [ t1 ] ~info

  let mk_nadd ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app (NAdd (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_nsub ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app (NSub (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_nmul ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app (NMul (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_ndiv ?(info = Dummy) m t1 t2 =
    Term.mk_fsym_app (NDiv (Ident.mk_fresh_svar (), m)) [ t1; t2 ] ~info

  let mk_nrem ?(info = Dummy) m t1 t2 =
    Term.mk_fsym_app (NRem (Ident.mk_fresh_svar (), m)) [ t1; t2 ] ~info

  let mk_npower ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app (NPower (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_ngeq ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app (NGeq (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_nleq ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app (NLeq (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_ngt ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app (NGt (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  let mk_nlt ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app (NLt (Ident.mk_fresh_svar ())) [ t1; t2 ] ~info

  (** Destruction *)

  let let_value = function
    | Term.FunApp (Value (n, _), [], info) -> (n, info)
    | _ -> assert false

  let let_nneg = function
    | Term.FunApp (NNeg _, [ t1 ], info) -> (t1, info)
    | _ -> assert false

  let let_nsext = function
    | Term.FunApp (NSEXT (size, _, ext, _), [ t1 ], info) ->
        (size, ext, t1, info)
    | _ -> assert false

  let let_nadd = function
    | Term.FunApp (NAdd _, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_nsub = function
    | Term.FunApp (NSub _, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_nmul = function
    | Term.FunApp (NMul _, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_ndiv = function
    | Term.FunApp (NDiv _, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_nrem = function
    | Term.FunApp (NRem _, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_npower = function
    | Term.FunApp (NPower _, [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_ngeq = function
    | Atom.App (Predicate.Psym (NGeq _), [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_nleq = function
    | Atom.App (Predicate.Psym (NLeq _), [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_ngt = function
    | Atom.App (Predicate.Psym (NGt _), [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  let let_nlt = function
    | Atom.App (Predicate.Psym (NLt _), [ t1; t2 ], info) -> (t1, t2, info)
    | _ -> assert false

  (** Observation *)

  let is_nneg = function Term.FunApp (NNeg _, _, _) -> true | _ -> false
  let is_nsext = function Term.FunApp (NSEXT _, _, _) -> true | _ -> false
  let is_nadd = function Term.FunApp (NAdd _, _, _) -> true | _ -> false
  let is_nsub = function Term.FunApp (NSub _, _, _) -> true | _ -> false
  let is_nmul = function Term.FunApp (NMul _, _, _) -> true | _ -> false
  let is_ndiv = function Term.FunApp (NDiv _, _, _) -> true | _ -> false
  let is_nrem = function Term.FunApp (NRem _, _, _) -> true | _ -> false
  let is_npower = function Term.FunApp (NPower _, _, _) -> true | _ -> false

  let is_ngeq = function
    | Atom.App (Predicate.Psym (NGeq _), _, _) -> true
    | _ -> false

  let is_nleq = function
    | Atom.App (Predicate.Psym (NLeq _), _, _) -> true
    | _ -> false

  let is_ngt = function
    | Atom.App (Predicate.Psym (NGt _), _, _) -> true
    | _ -> false

  let is_nlt = function
    | Atom.App (Predicate.Psym (NLt _), _, _) -> true
    | _ -> false

  let is_value = function Term.FunApp (Value _, _, _) -> true | _ -> false

  (** Function Symbols *)

  let fsym_of_num_fsym fsym = function
    | [ Sort.SVar _ ] -> fsym
    | [ T_int.SInt ] -> (
        match fsym with
        | Value (value, _) -> (
            try T_int.Int (Z.of_string value)
            with _ -> (
              try T_int.Int (Z.of_int @@ Q.to_int @@ Q.of_string value)
              with _ -> (
                try
                  T_int.Int
                    (Z.of_int @@ Q.to_int @@ Q.of_float @@ float_of_string value)
                with _ -> raise NotValue)))
        | NNeg _ -> T_int.Neg
        | NSEXT (_, _, _, _) -> failwith "not supported @ 1"
        | NAdd _ -> T_int.Add
        | NSub _ -> T_int.Sub
        | NMul _ -> T_int.Mul
        | NDiv (_, m) -> T_int.Div m
        | NRem (_, m) -> T_int.Rem m
        | NPower _ -> T_int.Power
        | _ -> fsym)
    | [ T_int.SInt; T_int.SInt ] -> (
        match fsym with NSEXT (_, _, _, _) -> T_int.Nop | _ -> fsym)
    | [ T_real.SReal ] -> (
        match fsym with
        | Value (value, _) -> (
            try T_real.Real (Q.of_string value)
            with _ -> (
              try T_real.Real (Q.of_float @@ float_of_string value)
              with _ -> raise NotValue))
        | NNeg _ -> T_real.RNeg
        | NSEXT (_, _, _, _) -> failwith "not supported @ 2"
        | NAdd _ -> T_real.RAdd
        | NSub _ -> T_real.RSub
        | NMul _ -> T_real.RMul
        | NDiv _ -> T_real.RDiv
        | NRem _ -> failwith "not supported @ 3"
        | NPower _ -> T_real.RPower
        | _ -> fsym)
    | [ T_bv.SBV size ] -> (
        match fsym with
        | Value (value, _) ->
            let z =
              try Z.of_string value
              with _ -> (
                try Z.of_int @@ Q.to_int @@ Q.of_string value
                with _ -> (
                  try
                    Z.of_int @@ Q.to_int @@ Q.of_float @@ float_of_string value
                  with _ -> raise NotValue))
            in
            let bits = T_bv.bits_of size in
            if required_bits z <= bits then T_bv.BVNum (size, int2bv bits z)
            else
              failwith
              @@ sprintf "%s is not representable in %d bits" value bits
        | NNeg _ -> T_bv.BVNeg size
        | NSEXT (_, _, _, _) -> failwith "not supported @ 4"
        | NAdd _ -> T_bv.BVAdd size
        | NSub _ -> T_bv.BVSub size
        | NMul _ -> T_bv.BVMul size
        | NDiv _ -> T_bv.BVDiv (size, Some true (*ToDo*))
        | NRem _ -> T_bv.BVRem (*ToDo*) (size, Some true (*ToDo*))
        | NPower _ -> failwith "not supported @ 5"
        | _ -> fsym)
    | [ T_bv.SBV _size1; T_bv.SBV _size2 ] -> (
        match fsym with
        | NSEXT (size, _, ext, _) ->
            (* assert (size1 = size && size2 = size + ext); *)
            T_bv.BVSEXT (size, ext)
        | _ -> fsym)
    | [ sort ] ->
        failwith @@ sprintf "sort %s is not num" (Term.str_of_sort sort)
    | sorts ->
        failwith
        @@ sprintf "not supported @ 6: %s, %s" (Term.str_of_funsym fsym)
             (String.concat_map_list ~sep:", " ~f:Term.str_of_sort sorts)

  let psym_of_num_psym psym = function
    | Sort.SVar _ -> psym
    | T_int.SInt -> (
        match psym with
        | NGeq _ -> T_int.Geq
        | NLeq _ -> T_int.Leq
        | NGt _ -> T_int.Gt
        | NLt _ -> T_int.Lt
        | _ -> psym)
    | T_real.SReal -> (
        match psym with
        | NGeq _ -> T_real.RGeq
        | NLeq _ -> T_real.RLeq
        | NGt _ -> T_real.RGt
        | NLt _ -> T_real.RLt
        | _ -> psym)
    | T_bv.SBV size -> (
        match psym with
        | NGeq _ -> T_bv.BVGeq (size, Some true (*ToDo*))
        | NLeq _ -> T_bv.BVLeq (size, Some true (*ToDo*))
        | NGt _ -> T_bv.BVGt (size, Some true (*ToDo*))
        | NLt _ -> T_bv.BVLt (size, Some true (*ToDo*))
        | _ -> psym)
    | sort -> failwith @@ sprintf "sort %s is not num" (Term.str_of_sort sort)
end

and T_ref : (Type.T_refType with type term := Term.t) = struct
  type Sort.t += SRef of Sort.t
  type fun_sym += Ref of Sort.t | Deref of Sort.t | Update of Sort.t

  (** Construction *)

  let mk_ref sort t = Term.mk_fsym_app (Ref sort) [ t ]
  let mk_deref sort t = Term.mk_fsym_app (Deref sort) [ t ]
  let mk_update sort t1 t2 = Term.mk_fsym_app (Update sort) [ t1; t2 ]

  (** Observation *)

  let is_ref_sort = function SRef _ -> true | _ -> false

  let eval_select = function
    | Term.FunApp (Ref _, [ e1 ], _) -> Some e1
    | _ -> None
end

and T_array :
  (Type.T_arrayType with type term := Term.t and type atom := Atom.t) = struct
  type fun_sym +=
    | AConst of Sort.t * Sort.t
    | AStore of Sort.t * Sort.t
    | ASelect of Sort.t * Sort.t

  type Sort.t += SArray of Sort.t * Sort.t

  let is_sarray = function SArray _ -> true | _ -> false
  let mk_array_sort s1 s2 = SArray (s1, s2)

  let rec of_arrow = function
    | Sort.SArrow (s, c) when Sort.is_pure_triple c ->
        mk_array_sort (of_arrow s) (of_arrow c.val_type)
    | s -> s

  let index_sort_of = function
    | SArray (si, _) -> si
    | _ -> failwith "not array sort"

  let elem_sort_of = function
    | SArray (_, se) -> se
    | _ -> failwith "not array sort"

  (** Construction *)

  let mk_const_array s1 s2 v = Term.mk_fsym_app (AConst (s1, s2)) [ v ]
  let mk_store s1 s2 a i e = Term.mk_fsym_app (AStore (s1, s2)) [ a; i; e ]
  let mk_select s1 s2 a i = Term.mk_fsym_app (ASelect (s1, s2)) [ a; i ]

  let of_fvar_app = function
    | Term.FunApp (FVar (tvar, sargs, sret), ts, _) ->
        let arr_sort = of_arrow @@ Sort.mk_fun (sargs @ [ sret ]) in
        List.fold_left ts ~init:(Term.mk_var tvar arr_sort) ~f:(fun arr t ->
            match Term.sort_of arr with
            | SArray (s1, s2) -> mk_select s1 s2 arr t
            | _ -> failwith "of_fvar_app")
    | t -> t

  (** Destruction *)

  let let_store = function
    | Term.FunApp (AStore (s1, s2), [ a; i; e ], info) -> (s1, s2, a, i, e, info)
    | _ -> assert false

  let let_select = function
    | Term.FunApp (ASelect (s1, s2), [ a; i ], info) -> (s1, s2, a, i, info)
    | _ -> assert false

  (** Observation *)

  let is_store = function Term.FunApp (AStore _, _, _) -> true | _ -> false
  let is_select = function Term.FunApp (ASelect _, _, _) -> true | _ -> false

  let rec eval_select arr i =
    match arr with
    | Term.FunApp (AConst _, [ e1 ], _) ->
        if false then
          print_endline
          @@ sprintf "eval select : %s [%s]->%s" (Term.str_of arr)
               (Term.str_of i) (Term.str_of e1);
        Some e1
    | Term.FunApp (AStore _, [ arr1; i1; e1 ], _) -> (
        if Stdlib.(i = i1) then (
          if false then
            print_endline
            @@ sprintf "eval select : %s [%s]->%s" (Term.str_of arr)
                 (Term.str_of i) (Term.str_of e1);
          Some e1)
        else
          match (i, i1) with
          | ( Term.FunApp (T_dt.DTCons (name1, _, _), _, _),
              Term.FunApp (T_dt.DTCons (name2, _, _), _, _) )
            when String.(name1 <> name2) ->
              eval_select arr1 i
          | _ -> (
              try
                if Stdlib.(Term.value_of i <> Term.value_of i1) then
                  eval_select arr1 i
                else None
              with _ -> None))
    (* | Term.FunApp (T_bool.Formula (Formula.Atom (atm, _)), _, _) when is_select_bool atm->
        let arr', i', _ = let_select_bool atm in
        aux @@ mk_select arr' i'
        | Term.FunApp (T_bool.Formula (Formula.Atom (atm, _)), _, _) when is_select_bool_neg atm->
        let arr', i', _ = let_select_bool_neg atm in
        aux @@ mk_select arr' i' *)
    | _ -> None

  let rec non_stored arr i =
    match arr with
    | Term.FunApp (AConst _, [ _ ], _) -> true
    | Term.FunApp (AStore _, [ arr1; i1; _ ], _) -> (
        if Stdlib.(i = i1) then false
        else
          match (i, i1) with
          | ( Term.FunApp (T_dt.DTCons (name1, _, _), _, _),
              Term.FunApp (T_dt.DTCons (name2, _, _), _, _) )
            when String.(name1 <> name2) ->
              non_stored arr1 i
          | _ -> (
              try
                if Stdlib.(Term.value_of i <> Term.value_of i1) then
                  non_stored arr1 i
                else false
              with _ -> false))
    | _ -> false
end

and T_tuple :
  (Type.T_tupleType with type term := Term.t and type atom := Atom.t) = struct
  type Sort.t += STuple of Sort.t list
  type fun_sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int
  type pred_sym += IsTuple of Sort.t list | NotIsTuple of Sort.t list

  (** Sorts *)

  let let_stuple = function STuple sorts -> sorts | _ -> assert false

  (** Construction *)

  let mk_tuple_cons sorts ts = Term.mk_fsym_app (TupleCons sorts) ts
  let mk_tuple_sel sorts t i = Term.mk_fsym_app (TupleSel (sorts, i)) [ t ]
  let mk_is_tuple sorts t = Atom.mk_psym_app (IsTuple sorts) [ t ]
  let mk_is_not_tuple sorts t = Atom.mk_psym_app (NotIsTuple sorts) [ t ]

  (** Destruction *)

  let let_tuple_cons = function
    | Term.FunApp (TupleCons sorts, ts, info) -> (sorts, ts, info)
    | _ -> assert false

  let let_tuple_sel = function
    | Term.FunApp (TupleSel (sorts, i), [ t ], info) -> (sorts, i, t, info)
    | _ -> assert false

  (** Observation *)

  let is_tuple_cons = function
    | Term.FunApp (TupleCons _, _, _) -> true
    | _ -> false

  let is_tuple_sel = function
    | Term.FunApp (TupleSel _, _, _) -> true
    | _ -> false

  let eval_select tup i =
    match tup with
    | Term.FunApp (TupleCons _, ts, _) -> Some (List.nth_exn ts i)
    | _ -> None
end

and T_dt :
  (Type.T_dtType
    with type term := Term.t
     and type atom := Atom.t
     and type formula := Formula.t
     and type dtenv := DTEnv.t
     and type dt := Datatype.t
     and type dtcons := Datatype.cons
     and type dtsel := Datatype.sel
     and type flag := Datatype.flag) = struct
  type fun_sym +=
    | DTSel of string * Datatype.t * Sort.t
    | DTCons of string * Sort.t list * Datatype.t

  type pred_sym +=
    | IsCons of string * Datatype.t
    | NotIsCons of string * Datatype.t

  type Sort.t += SDT of Datatype.t | SUS of string * Sort.t list

  let params_of = function SDT dt -> Datatype.params_of dt | _ -> assert false
  let is_sdt = function SDT _ -> true | _ -> false
  let is_sus = function SUS _ -> true | _ -> false
  let is_dt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_codt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_undef = function SUS (_, _) -> true | _ -> false

  let rec is_finite_dt ?(his = []) sort =
    if List.exists his ~f:(Stdlib.( = ) sort) then false
    else
      match sort with
      | SDT dt ->
          List.for_all (Datatype.conses_of dt) ~f:(fun cons ->
              let args = Datatype.sorts_of_cons dt cons in
              List.for_all args ~f:(is_finite_dt ~his:(sort :: his)))
      (* | T_bool.SBool -> true *)
      | _ -> false

  (** Construction *)

  let mk_cons ?(info = Dummy) dt name terms =
    match Datatype.look_up_cons dt name with
    | Some cons ->
        let fsym = Datatype.fsym_of_cons dt cons in
        Term.mk_fsym_app fsym terms ~info
    | _ -> failwith @@ "unknown cons :" ^ name

  let mk_sel ?(info = Dummy) dt name term =
    match Datatype.look_up_sel dt name with
    | Some sel ->
        let fsym = Datatype.fsym_of_sel dt sel in
        Term.mk_fsym_app fsym [ term ] ~info
    | _ -> failwith @@ "unknown sel :" ^ name

  let mk_sel_by_cons ?(info = Dummy) dt cons_name i term =
    match Datatype.look_up_cons dt cons_name with
    | Some cons ->
        let sel = List.nth_exn (Datatype.sels_of_cons cons) i in
        let fsym = Datatype.fsym_of_sel dt sel in
        Term.mk_fsym_app fsym [ term ] ~info
    | _ -> failwith @@ "unknown cons :" ^ cons_name

  let mk_is_cons ?(info = Dummy) dt name term =
    Atom.mk_psym_app (IsCons (name, dt)) [ term ] ~info

  let mk_is_not_cons ?(info = Dummy) dt name term =
    Atom.mk_psym_app (NotIsCons (name, dt)) [ term ] ~info

  let rec mk_dummy = function
    | SDT dt when Datatype.is_dt dt -> (
        match Datatype.look_up_base_cons dt with
        | Some cons ->
            let sorts = Datatype.sorts_of_cons dt cons in
            mk_cons dt (Datatype.name_of_cons cons) (List.map sorts ~f:mk_dummy)
        | None -> assert false)
    | SUS (name, _) as sort ->
        let name = "dummy_" ^ name in
        add_dummy_term (Ident.Tvar name) sort;
        Term.mk_var (Ident.Tvar name) sort
    | sort -> Term.mk_dummy sort

  (** Observation *)

  let is_cons = function Term.FunApp (DTCons _, _, _) -> true | _ -> false
  let is_sel = function Term.FunApp (DTSel _, _, _) -> true | _ -> false

  let is_is_cons = function
    | Atom.App (Predicate.Psym (IsCons _), _, _) -> true
    | _ -> false

  let is_is_not_cons = function
    | Atom.App (Predicate.Psym (NotIsCons _), _, _) -> true
    | _ -> false

  let sels_of_cons = function
    | DTCons (name, _, dt) -> (
        match Datatype.look_up_cons dt name with
        | Some cons -> Datatype.sels_of_cons cons
        | _ -> assert false)
    | _ -> assert false

  let base_terms_of dt =
    List.map (Datatype.base_conses_of dt) ~f:(fun cons ->
        mk_cons dt cons.name [])

  let size_of_cons t =
    let size = ref 0 in
    ignore
    @@ Term.map_term true t ~f:(function
         | Term.FunApp (DTCons _, _, _) as t ->
             incr size;
             t
         | t -> t);
    !size

  let inst_unknown_sel_term simplify_term =
    Formula.map_term
      ~f:
        ( simplify_term >> function
          | Term.FunApp (DTSel (_, _, sort), _, _) -> Term.mk_dummy sort
          | t -> t )

  let eval_select sel_name dt = function
    | Term.FunApp (DTCons (cons_name, _, _), ts, _) -> (
        match Datatype.look_up_cons dt cons_name with
        | Some cons ->
            List.fold2_exn (Datatype.sels_of_cons cons) ts ~init:None
              ~f:(fun ret sel t ->
                match ret with
                | Some _ -> ret
                | None ->
                    if String.(Datatype.name_of_sel sel = sel_name) then Some t
                    else None)
        | None -> failwith @@ cons_name ^ " not found")
    | _ -> None
end

and Datatype :
  (Type.DatatypeType with type term := Term.t and type formula := Formula.t) =
struct
  type sel = Sel of string * Sort.t | InSel of string * string * Sort.t list
  type cons = { name : string; sels : sel list }
  type func = FCons of cons | FSel of sel
  type flag = FDt | FCodt | Undef | Alias of Sort.t
  type dt = { name : string; params : Sort.t list; conses : cons list }

  type t = {
    name : string;
    dts : dt list; (* mutually defined datatypes including name *)
    flag : flag;
  }

  (** Construction *)

  let mk_cons ?(sels = []) name = { name; sels }
  let mk_sel name ret_sort = Sel (name, ret_sort)
  let mk_insel name ret_name params = InSel (name, ret_name, params)
  let mk_dt name params = { name; params; conses = [] }
  let make name dts flag = { name; dts; flag }

  let mk_uninterpreted_datatype ?(numeral = 0) name =
    make name
      [ mk_dt name @@ List.init numeral ~f:(fun _ -> Sort.mk_fresh_svar ()) ]
      Undef

  let mk_alias name sort = make name [] (Alias sort)

  let enum_cons_terms depth sort terms =
    let rec inner depth dts sort_term_map =
      if depth = 0 then sort_term_map
      else
        inner (depth - 1) dts
        @@ Set.fold dts ~init:sort_term_map ~f:(fun acc dt ->
               let terms =
                 Set.filter ~f:(fun t -> T_dt.size_of_cons t <= depth + 1)
                 @@ Set.Poly.union_list
                 @@ List.filter_map (Datatype.conses_of dt) ~f:(fun cons ->
                        match Datatype.sorts_of_cons dt cons with
                        | [] ->
                            Some
                              (Set.Poly.singleton
                              @@ T_dt.mk_cons dt cons.name [])
                        | sorts ->
                            if
                              List.for_all sorts ~f:(fun s1 ->
                                  Map.Poly.existsi sort_term_map
                                    ~f:(fun ~key:s2 ~data ->
                                      Stdlib.(s1 = s2)
                                      && Fn.non Set.is_empty data))
                            then
                              Option.return
                              @@ Set.Poly.map ~f:(T_dt.mk_cons dt cons.name)
                              @@ List.fold sorts ~init:(Set.Poly.singleton [])
                                   ~f:(fun acc sort ->
                                     Set.concat_map ~f:(fun term ->
                                         Set.Poly.map acc ~f:(fun ts ->
                                             ts @ [ term ]))
                                     @@ Map.Poly.find_exn sort_term_map sort)
                            else None)
               in
               let key = T_dt.SDT dt in
               match Map.Poly.find acc key with
               | Some v -> Map.Poly.set acc ~key ~data:(Set.union v terms)
               | None -> Map.Poly.add_exn acc ~key ~data:terms)
    in
    let sorts = Term.sorts_of_sort sort in
    let dts =
      Set.Poly.filter_map sorts ~f:(function
        | T_dt.SDT dt -> Some dt
        | _ -> None)
    in
    let sort_term_map =
      let init =
        Map.of_set_exn
        @@ Set.Poly.map sorts ~f:(fun s ->
               (s, Set.Poly.singleton (Term.mk_dummy s)))
      in
      Set.fold terms ~init ~f:(fun acc term ->
          let key = Term.sort_of term in
          match Map.Poly.find acc key with
          | Some v -> Map.Poly.set acc ~key ~data:(Set.add v term)
          | None -> Map.Poly.add_exn acc ~key ~data:(Set.Poly.singleton term))
    in
    Map.Poly.find_exn (inner depth dts sort_term_map) sort

  (** Observation *)

  let name_of_sel = function Sel (name, _) | InSel (name, _, _) -> name
  let sels_of_cons (cons : cons) = cons.sels
  let name_of_cons (cons : cons) = cons.name

  let look_up_sel_of_cons cons name =
    List.find (sels_of_cons cons) ~f:(name_of_sel >> String.( = ) name)

  let name_of_dt (dt : dt) = dt.name
  let params_of_dt (dt : dt) = dt.params
  let conses_of_dt (dt : dt) = dt.conses

  let full_name_of_dt dt =
    String.concat_map_list_append ~sep:", " (params_of_dt dt)
      ~f:Term.str_of_sort (name_of_dt dt)

  let name_of t = t.name
  let flag_of t = t.flag
  let dts_of t = t.dts

  let look_up_dt t name =
    List.find (dts_of t) ~f:(name_of_dt >> String.( = ) name)

  let dt_of t =
    match look_up_dt t @@ name_of t with
    | Some dt -> dt
    | _ -> failwith @@ sprintf "unknown dt: %s" (name_of t)

  let conses_of t = conses_of_dt @@ dt_of t

  let base_conses_of t =
    List.filter (conses_of t) ~f:(sels_of_cons >> List.is_empty)

  let sels_of t = List.concat_map (conses_of t) ~f:sels_of_cons
  let params_of t = params_of_dt @@ dt_of t

  let look_up_cons t name =
    List.find (conses_of t) ~f:(name_of_cons >> String.( = ) name)

  let look_up_sel t name =
    List.find_map (conses_of t) ~f:(Fn.flip look_up_sel_of_cons name)

  let look_up_cons_of_sel t name =
    List.find (conses_of t)
      ~f:(sels_of_cons >> List.exists ~f:(name_of_sel >> String.( = ) name))

  let look_up_func t name =
    match look_up_cons t name with
    | Some cons -> Some (FCons cons)
    | None -> (
        match look_up_sel t name with
        | Some sel -> Some (FSel sel)
        | None -> None)

  let look_up_base_cons t =
    let has_direct_base t =
      List.exists (conses_of t)
        ~f:
          (sels_of_cons
          >> List.for_all ~f:(function Sel _ -> true | InSel _ -> false))
    in
    let rec look_up_other_base t his =
      if List.exists his ~f:(name_of >> String.( = ) @@ name_of t) then None
      else
        conses_of t
        |> List.sort ~compare:(fun cons1 cons2 ->
               let sels1, sels2 = (sels_of_cons cons1, sels_of_cons cons2) in
               if List.length sels1 < List.length sels2 then -1
               else if List.length sels1 > List.length sels2 then 1
               else 0)
        |> List.find ~f:(fun cons ->
               List.for_all (sels_of_cons cons) ~f:(function
                 | Sel _ -> true
                 | InSel (_, ret_name, _) ->
                     let ret_dt = { t with name = ret_name } in
                     if has_direct_base ret_dt then true
                     else Option.is_some @@ look_up_other_base ret_dt (t :: his)))
    in
    List.find (conses_of t) ~f:(fun cons ->
        List.for_all (sels_of_cons cons) ~f:(function
          | Sel _ -> true
          | InSel (_, ret_name, _) ->
              Option.is_some
              @@ look_up_other_base { t with name = ret_name } [ t ]))

  let full_name_of t =
    String.concat_map_list_append ~sep:", " (params_of t) ~f:Term.str_of_sort
      (name_of t)

  let short_name_of t =
    let name = String.prefix (name_of t) 1 in
    let params = params_of t in
    if List.is_empty params then name
    else
      sprintf "%s%s"
        (String.paren
        @@ String.concat_map_list ~sep:"," params ~f:Term.short_name_of_sort)
        name

  let sort_of t =
    match flag_of t with
    | Undef -> T_dt.SUS (name_of t, params_of t)
    | Alias s -> s
    | _ -> T_dt.SDT t

  let svs_of t =
    Set.Poly.union_list @@ List.map ((*ToDo*) params_of t) ~f:Term.svs_of_sort

  let evs_of t =
    Set.Poly.union_list @@ List.map ((*ToDo*) params_of t) ~f:Term.evs_of_sort

  let rvs_of t =
    Set.Poly.union_list @@ List.map ((*ToDo*) params_of t) ~f:Term.rvs_of_sort

  let pat_match_sort dt1 dt2 =
    if String.(dt1.name = dt2.name) then
      let omaps, smaps, emaps =
        List.unzip3
        @@ List.map2_exn (params_of dt1) (params_of dt2) ~f:Term.pat_match_sort
      in
      ( Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps )
    else (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)

  let is_dt t = match flag_of t with FDt -> true | _ -> false
  let is_codt t = match flag_of t with FCodt -> true | _ -> false
  let is_undef t = match flag_of t with Undef -> true | _ -> false
  let is_alias t = match flag_of t with Alias _ -> true | _ -> false

  let rec is_poly t =
    List.exists (params_of t) ~f:(function
      | Sort.SVar _ -> true
      | T_dt.SDT t1 -> is_poly t1
      | _ -> false)

  let is_base t name =
    match look_up_cons t name with
    | Some cons -> List.is_empty cons.sels
    | None -> false

  let is_sel = function Sel _ -> true | _ -> false
  let is_insel = function InSel _ -> true | _ -> false
  let is_fcons = function FCons _ -> true | _ -> false
  let is_fsel = function FSel _ -> true | _ -> false

  (** Printing *)

  let str_of_sel = function
    | Sel (name, ret_sort) -> sprintf "%s : %s" name (Term.str_of_sort ret_sort)
    | InSel (name, ret_name, params) ->
        sprintf "%s : %s" name @@ full_name_of_dt @@ mk_dt ret_name params

  let str_of_cons cons =
    sprintf "%s (%s)" (name_of_cons cons)
    @@ String.concat_map_list ~sep:", " ~f:str_of_sel
    @@ sels_of_cons cons

  let str_of_flag = function
    | FDt -> "data"
    | FCodt -> "codata"
    | Undef -> "extern"
    | Alias _ -> "alias"

  let str_of t =
    match flag_of t with
    | Undef -> sprintf "data %s" (name_of t)
    | Alias s -> sprintf "data %s = %s" (name_of t) (Term.str_of_sort s)
    | flag ->
        sprintf "%s %s where [%s]" (str_of_flag flag) (full_name_of t)
        @@ String.concat_map_list ~sep:" and " (dts_of t) ~f:(fun dt ->
               sprintf "%s %s = %s" (str_of_flag flag) (full_name_of_dt dt)
               (*String.concat_map_list ~sep:" " ~f:Term.str_of_sort @@ params_of_dt dt)*)
               @@ String.concat_map_list ~sep:" | " ~f:str_of_cons
               @@ conses_of_dt dt)

  let full_str_of_sel t = function
    | Sel (name, ret_sort) -> sprintf "%s : %s" name (Term.str_of_sort ret_sort)
    | InSel (name, ret_name, _) ->
        sprintf "%s : %s" name @@ full_name_of { t with name = ret_name }

  let full_str_of_cons t cons =
    sprintf "%s (%s)" (name_of_cons cons)
    @@ String.concat_map_list ~sep:", " ~f:(full_str_of_sel t)
    @@ sels_of_cons cons

  (** Transformation *)

  let update_name t name = { t with name }
  let update_dts t dts = { t with dts }

  let rec update_dts_with_dt dts dt =
    match dts with
    | [] -> []
    | dt1 :: tl ->
        if String.(name_of_dt dt1 = name_of_dt dt) then dt :: tl
        else dt1 :: update_dts_with_dt tl dt

  let update_dt t dt = { t with dts = update_dts_with_dt (dts_of t) dt }

  let add_cons t cons =
    let dt = dt_of t in
    update_dt t { dt with conses = cons :: conses_of_dt dt }

  let add_sel cons sel = { cons with sels = sel :: sels_of_cons cons }
  let update_conses t conses = update_dt t { (dt_of t) with conses }

  let rec update_params t params =
    let dt = dt_of t in
    (*print_endline @@ sprintf "update dt params: %s with {%s}" (full_name_of_dt dt) (String.concat_map_list ~sep:" " ~f:Term.str_of_sort params);*)
    let omap, smap, emap =
      let omaps, smaps, emaps =
        try
          List.unzip3
          @@ List.map2_exn (params_of_dt dt) params ~f:Term.pat_match_sort
        with _ ->
          failwith
          @@ sprintf "[update_params] %s with {%s}" (full_name_of_dt dt)
               (String.concat_map_list ~sep:" " ~f:Term.str_of_sort params)
      in
      ( Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps )
    in
    let ret = update_dt t @@ subst_dt (omap, smap, emap) dt in
    (*print_endline @@ sprintf "after update: %s" @@ str_of ret;*)
    ret

  and subst_sorts_dt smap dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel
                        ( name,
                          ret_name,
                          List.map params ~f:(Term.subst_sorts_sort smap) )
                  | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_sorts_sort smap ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:(Term.subst_sorts_sort smap);
    }

  and subst_conts_dt emap dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel
                        ( name,
                          ret_name,
                          List.map params ~f:(Term.subst_conts_sort emap) )
                  | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_conts_sort emap ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:(Term.subst_conts_sort emap);
    }

  and subst_opsigs_dt omap dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel
                        ( name,
                          ret_name,
                          List.map params ~f:(Term.subst_opsigs_sort omap) )
                  | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_opsigs_sort omap ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:(Term.subst_opsigs_sort omap);
    }

  and subst_dt maps dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel
                        ( name,
                          ret_name,
                          List.map params ~f:(Term.subst_sort maps) )
                  | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_sort maps ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:(Term.subst_sort maps);
    }

  let subst_sorts smap dt =
    update_params dt @@ List.map ~f:(Term.subst_sorts_sort smap) @@ params_of dt

  let subst_conts emap dt =
    update_params dt @@ List.map ~f:(Term.subst_conts_sort emap) @@ params_of dt

  let subst_opsigs omap dt =
    update_params dt
    @@ List.map ~f:(Term.subst_opsigs_sort omap)
    @@ params_of dt

  let subst maps dt =
    update_params dt @@ List.map ~f:(Term.subst_sort maps) @@ params_of dt

  let fresh_conts_sort_dt dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel
                        ( name,
                          ret_name,
                          List.map params ~f:Term.fresh_conts_sort )
                  | Sel (name, ret_sort) ->
                      Sel (name, Term.fresh_conts_sort ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:Term.fresh_conts_sort;
    }

  let fresh_rvs_sort_dt dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel
                        (name, ret_name, List.map params ~f:Term.fresh_rvs_sort)
                  | Sel (name, ret_sort) ->
                      Sel (name, Term.fresh_rvs_sort ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:Term.fresh_rvs_sort;
    }

  let fresh_conts_sort t =
    { t with dts = List.map ~f:fresh_conts_sort_dt t.dts }

  let fresh_rvs_sort t = { t with dts = List.map ~f:fresh_rvs_sort_dt t.dts }

  let fresh_of t =
    let rec update_dt_params t dt params his =
      (*(match his with
        | [_] ->
         print_endline @@ sprintf ">>>>>update dt params:%s with {%s}" (full_name_of_dt dt) (String.concat_map_list ~sep:" " ~f:Term.str_of_sort params)
        | _ ->
         print_endline @@ sprintf ">>>>>>>>>>>update dt params:%s with {%s}" (full_name_of_dt dt) (String.concat_map_list ~sep:" " ~f:Term.str_of_sort params));*)
      let conses' =
        List.fold2_exn (params_of_dt dt) params ~init:(conses_of_dt dt)
          ~f:(fun conses arg1 arg ->
            List.map conses ~f:(fun cons ->
                let sels' =
                  List.map (sels_of_cons cons) ~f:(function
                    | Sel (name, (Sort.SVar _ as svar))
                      when Stdlib.(svar = arg1) -> (
                        match arg with
                        | T_dt.SDT t1 -> (
                            match look_up_dt t (name_of t1) with
                            | Some _ -> InSel (name, name_of t1, params_of t1)
                            | _ -> Sel (name, arg))
                        | _ -> Sel (name, arg))
                    | InSel (name, ret_name, params1) ->
                        InSel
                          ( name,
                            ret_name,
                            if String.(ret_name = name_of_dt dt) then params
                            else params1 )
                    | sel -> sel)
                in
                { cons with sels = sels' }))
      in
      ( List.fold_left conses' ~init:t ~f:(fun t cons ->
            List.fold_left (sels_of_cons cons) ~init:t ~f:(fun t -> function
              | Sel _ -> t
              | InSel (_, ret_sort, params) ->
                  if not @@ List.exists his ~f:(Stdlib.( = ) ret_sort) then
                    let t', dt' =
                      update_dt_params (update_name t ret_sort)
                        (dt_of @@ update_name t ret_sort)
                        params (ret_sort :: his)
                    in
                    update_name (update_dt t' dt') (name_of t)
                  else t)),
        { dt with params; conses = conses' } )
    in
    let dts' =
      List.map (dts_of t) ~f:(fun dt ->
          let params' =
            List.map (params_of_dt dt) ~f:(function
              | Sort.SVar _ -> Sort.mk_fresh_svar ()
              | arg -> arg)
          in
          snd @@ update_dt_params t dt params' [])
    in
    { t with dts = dts' }

  (** Observation *)

  let sort_of_sel t = function
    | Sel (_, sort) -> sort
    | InSel (_, ret_name, params) -> (
        match look_up_dt t ret_name with
        | Some _ -> sort_of @@ update_params { t with name = ret_name } params
        | None -> failwith @@ sprintf "unknown sort: %s" ret_name)

  let sorts_of_cons t cons = List.map (sels_of_cons cons) ~f:(sort_of_sel t)

  let sorts_of_cons_name t cons_name =
    match look_up_cons t cons_name with
    | Some cons -> sorts_of_cons t cons
    | _ -> failwith @@ sprintf "%s not found" cons_name

  let full_dts_of t =
    dts_of
    @@ List.fold_left (conses_of t) ~init:t ~f:(fun ret cons ->
           List.fold_left (sels_of_cons cons) ~init:ret ~f:(fun ret -> function
             | InSel (_, ret_name, params) ->
                 if String.(name_of t <> ret_name) then
                   update_params (update_name ret ret_name) params
                 else ret
             | Sel _ -> ret))

  let is_finite t =
    not
    @@ List.exists (conses_of t) ~f:(fun cons ->
           List.for_all (sorts_of_cons t cons) ~f:(fun arg ->
               Stdlib.(arg = T_dt.SDT t) && T_dt.is_finite_dt arg))

  let rec is_singleton = function
    | T_dt.SDT t as sort -> (
        match conses_of t with
        | [ cons ] ->
            List.for_all (sorts_of_cons t cons) ~f:(fun arg ->
                Stdlib.(arg = sort) || is_singleton arg)
        | _ -> false)
    | _ -> false

  let fsym_of_cons t cons =
    (* let t = fresh_of t in *)
    match look_up_cons t @@ name_of_cons cons with
    | Some cons -> T_dt.DTCons (name_of_cons cons, sorts_of_cons t cons, t)
    | None -> assert false

  let fsym_of_sel t sel =
    (* let t = fresh_of t in *)
    match look_up_sel t @@ name_of_sel sel with
    | None -> assert false
    | Some (Sel (name, ret_sort)) -> T_dt.DTSel (name, t, ret_sort)
    | Some (InSel (name, ret_name, params)) -> (
        match look_up_dt t ret_name with
        | Some _ ->
            T_dt.DTSel
              (name, t, sort_of @@ update_params (update_name t ret_name) params)
        | None -> failwith @@ sprintf "unknown dt sort:%s" ret_name)

  let fsym_of_func t = function
    | FCons cons -> fsym_of_cons t cons
    | FSel sel -> fsym_of_sel t sel

  let size_of_cons dt cons =
    1
    + (List.length
      @@ List.filter ~f:(sort_of_sel dt >> T_dt.is_sdt)
      @@ sels_of_cons cons)

  let used_dt_and_sorts_of dt =
    let rec inner visited dt ret =
      if Set.mem visited dt then (visited, ret)
      else
        let visited = Set.add visited dt in
        let sorts =
          Set.Poly.of_list
          @@ List.concat_map (conses_of dt) ~f:(sorts_of_cons dt)
        in
        let ret = Set.union ret sorts in
        let dts =
          Set.Poly.filter_map sorts ~f:(function
            | T_dt.SDT dt -> Some dt
            | _ -> None)
        in
        Set.fold dts ~init:(visited, ret) ~f:(fun (visited, ret) dt ->
            inner visited dt ret)
    in
    inner Set.Poly.empty dt Set.Poly.empty

  let size_fun_var_of dt = Ident.Tvar (sprintf "SizeOf_%s" (name_of dt))

  (** TODO: Now assume [dt] is a monotype datatype, support polytype in future

      let rec SizeOf_dt (x:dt) = if is_cons_0 x then 1 +
      SizeOf_(typeof(sel_01))(sel_01(x)) + ... +
      SizeOf_(typeof(sel_0n))(sel_0n(x)) ... else if is_cons_m x then 1 +
      SizeOf(typeof(sel_m1))(sel_m1(x)) + ... +
      SizeOf(typeof(sel_mp))(sel_mp(x)) else 1

      property: forall x:dt. (is_cons_0 x => SizeOf_dt(x) >= 1 + |sels_0|) /\
      ... /\ (is_cons_m x => SizeOf_dt(x) >= 1 + |sels_m|)*)
  let size_fun_of dt =
    let min_size_of = function
      | T_dt.SDT dt ->
          Integer.min_list @@ List.map (conses_of dt) ~f:(size_of_cons dt)
      | _ -> 0
    in
    let term_of_sel x sel =
      match sort_of_sel dt sel with
      | T_dt.SDT dt1 ->
          let t = T_dt.mk_sel dt (name_of_sel sel) x in
          Term.mk_fvar_app (size_fun_var_of dt1) [ T_dt.SDT dt1 ] T_int.SInt
            [ t ]
      | _ -> T_int.zero ()
    in
    let conses = conses_of dt in
    let fun_var = size_fun_var_of dt in
    let x = Term.mk_var (Ident.Tvar "x") (T_dt.SDT dt) in
    let params = [ (Ident.Tvar "x", T_dt.SDT dt) ] in
    let def =
      List.fold_right conses ~init:(T_int.zero ()) ~f:(fun cons acc ->
          let sels = sels_of_cons cons in
          T_bool.ifte
            (Formula.mk_atom @@ T_dt.mk_is_cons dt cons.name x)
            (List.fold sels ~init:(T_int.one ()) ~f:(fun acc sel ->
                 T_int.mk_add acc (term_of_sel x sel)))
            acc)
    in
    let prop =
      Formula.mk_forall params @@ Formula.and_of
      @@ List.map conses ~f:(fun cons ->
             let min_size =
               List.map (sels_of_cons cons) ~f:(sort_of_sel dt >> min_size_of)
               |> List.fold ~init:1 ~f:( + )
             in
             Formula.mk_imply (Formula.mk_atom @@ T_dt.mk_is_cons dt cons.name x)
             @@ Formula.geq
                  (Term.mk_fvar_app fun_var (List.map ~f:snd params) T_int.SInt
                     [ x ])
                  (T_int.mk_int @@ Z.of_int min_size))
    in
    (fun_var, (params, T_int.SInt, def, true, prop))

  let app_size_fun dt x =
    Term.mk_fvar_app (size_fun_var_of dt) [ T_dt.SDT dt ] T_int.SInt [ x ]

  (** Datatypes *)

  let mk_name_of_sel cons_name i = sprintf "%s#%d" cons_name i

  let mk_unit_dt () =
    let dt = make "unit" [ mk_dt "unit" [] ] FDt in
    add_cons dt (mk_cons "()")

  let mk_option_dt () =
    let param = Sort.mk_fresh_svar () in
    let dt = make "option" [ mk_dt "option" [ param ] ] FDt in
    let dt = add_cons dt (mk_cons "None") in
    add_cons dt
      (mk_cons "Some" ~sels:[ mk_sel (mk_name_of_sel "Some" 0) param ])

  let mk_list_dt () =
    let param = Sort.mk_fresh_svar () in
    let dt = make "list" [ mk_dt "list" [ param ] ] FDt in
    let dt = add_cons dt @@ mk_cons "[]" in
    add_cons dt
    @@ mk_cons "::"
         ~sels:
           [
             mk_sel (mk_name_of_sel "::" 0) param;
             mk_insel (mk_name_of_sel "::" 1) "list" [ param ];
           ]

  let mk_exn_dt () = make "exn" [ mk_dt "exn" [] ] Undef
  let mk_unit () = T_dt.mk_cons (mk_unit_dt ()) "()" []
  let mk_unit_sort () = sort_of (mk_unit_dt ())

  let is_unit_sort = function
    | T_dt.SDT dt -> Stdlib.(dt = mk_unit_dt ())
    | _ -> false

  let is_option_sort = function
    | T_dt.SDT dt -> String.(dt.name = "option") (*ToDo*)
    | _ -> false

  let is_list_sort = function
    | T_dt.SDT dt -> String.(dt.name = "list") (*ToDo*)
    | _ -> false

  let is_exn_sort = function
    | T_dt.SDT dt -> Stdlib.(dt = mk_exn_dt ())
    | _ -> false
end

and T_string : (Type.T_stringType with type term := Term.t) = struct
  type Sort.t += SString
  type fun_sym += StrConst of string

  let make str = Term.mk_fsym_app (StrConst str) []

  let let_string_const = function
    | Term.FunApp (StrConst str, _, info) -> (str, info)
    | _ -> assert false
end

and T_sequence :
  (Type.T_sequenceType with type term := Term.t and type atom := Atom.t) =
struct
  type Sort.t += SSequence of bool

  type fun_sym +=
    | SeqEpsilon
    | SeqSymbol of string
    | SeqConcat of bool (* the first argument must be finite *)
    | SeqLeftQuotient of bool (* the first argument must be finite *)
    | SeqRightQuotient of bool (* the first argument must be finite *)

  type pred_sym +=
    | IsPrefix of bool
    | NotIsPrefix of bool
    | SeqInRegExp of bool * string Grammar.RegWordExp.t
    | NotSeqInRegExp of bool * string Grammar.RegWordExp.t

  let mk_eps () = Term.mk_fsym_app SeqEpsilon []
  let mk_symbol symbol = Term.mk_fsym_app (SeqSymbol symbol) []
  let mk_concat ~fin t1 t2 = Term.mk_fsym_app (SeqConcat fin) [ t1; t2 ]
  let mk_is_prefix fin t1 t2 = Atom.mk_psym_app (IsPrefix fin) [ t1; t2 ]
  let mk_is_not_prefix fin t1 t2 = Atom.mk_psym_app (NotIsPrefix fin) [ t1; t2 ]

  let mk_is_in_regexp fin regexp t =
    Atom.mk_psym_app (SeqInRegExp (fin, regexp)) [ t ]

  let mk_is_not_in_regexp fin regexp t =
    Atom.mk_psym_app (NotSeqInRegExp (fin, regexp)) [ t ]
end

and T_regex :
  (Type.T_regexType with type term := Term.t and type atom := Atom.t) = struct
  type Sort.t += SRegEx

  type fun_sym +=
    | RegEmpty
    | RegFull
    | RegEpsilon
    | RegStr
    | RegComplement
    | RegStar
    | RegPlus
    | RegOpt
    | RegConcat
    | RegUnion
    | RegInter

  type pred_sym += StrInRegExp | NotStrInRegExp

  let mk_empty ?(info = Dummy) () = Term.mk_fsym_app ~info RegEmpty []
  let mk_full ?(info = Dummy) () = Term.mk_fsym_app ~info RegFull []
  let mk_eps ?(info = Dummy) () = Term.mk_fsym_app ~info RegEpsilon []
  let mk_str_to_re ?(info = Dummy) t1 = Term.mk_fsym_app ~info RegStr [ t1 ]

  let mk_complement ?(info = Dummy) t1 =
    Term.mk_fsym_app ~info RegComplement [ t1 ]

  let mk_star ?(info = Dummy) t1 = Term.mk_fsym_app ~info RegStar [ t1 ]
  let mk_plus ?(info = Dummy) t1 = Term.mk_fsym_app ~info RegPlus [ t1 ]
  let mk_opt ?(info = Dummy) t1 = Term.mk_fsym_app ~info RegOpt [ t1 ]

  let mk_concat ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app ~info RegConcat [ t1; t2 ]

  let mk_union ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app ~info RegUnion [ t1; t2 ]

  let mk_inter ?(info = Dummy) t1 t2 =
    Term.mk_fsym_app ~info RegInter [ t1; t2 ]

  let mk_str_in_regexp ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app ~info StrInRegExp [ t1; t2 ]

  let mk_not_str_in_regexp ?(info = Dummy) t1 t2 =
    Atom.mk_psym_app ~info NotStrInRegExp [ t1; t2 ]
end

and TermSubst : (Type.TermSubstType with type term := Term.t) = struct
  type t = (Ident.tvar, Term.t) Map.Poly.t

  let str_of subst =
    String.concat_map_list ~sep:", " (Map.Poly.to_alist subst)
      ~f:(fun (x, term) ->
        sprintf "%s |-> %s" (Ident.str_of_tvar x) (Term.str_of term))

  let make ~name senv args =
    try
      (* ToDo : check whether args match sorts *)
      Map.Poly.of_alist_exn @@ List.zip_exn (List.map senv ~f:fst) args
    with e ->
      printf "name: %s #senv: %d #args: %d" name (List.length senv)
        (List.length args);
      raise e
end

and PredSubst : (Type.PredSubstType with type formula := Formula.t) = struct
  type t = (Ident.pvar, sort_env_list * Formula.t) Map.Poly.t
end

and FuncSubst : (Type.FuncSubstType with type term := Term.t) = struct
  type t = (Ident.tvar, sort_env_list * Term.t) Map.Poly.t
end

and FunEnv :
  (Type.FunEnvType with type term := Term.t and type formula := Formula.t) =
struct
  type t =
    (Ident.tvar, sort_env_list * Sort.t * Term.t * bool * Formula.t) Map.Poly.t

  let mk_empty () = Map.Poly.empty

  let property_of (fenv : t) phi =
    if Map.Poly.is_empty fenv then Formula.mk_true ()
    else
      let recterms =
        Formula.filtered_terms_of phi ~f:(function
          | Term.FunApp (FVar (v, _, _), _, _) -> Map.Poly.mem fenv v
          | _ -> false)
      in
      Formula.and_of @@ Set.to_list
      @@ Set.Poly.filter_map recterms ~f:(function
           | Term.FunApp (FVar (v, _, _), args, _) -> (
               match Map.Poly.find fenv v with
               | Some (_, _, _, _, property) when Formula.is_bind property ->
                   let _, env, phi, _ = Formula.let_bind property in
                   let sub =
                     Map.of_list_exn
                     @@ List.map2_exn env args ~f:(fun (tvar, _) t -> (tvar, t))
                   in
                   Some (Formula.subst sub phi)
               | _ -> None)
           | _ -> None)

  let defined_atom_formula_of polarity (fenv : t) phi =
    assert (Formula.is_atom phi);
    if Map.Poly.is_empty fenv then phi
    else
      let property = property_of fenv phi in
      if Formula.is_true property then
        if polarity then phi else Formula.mk_neg phi
      else if polarity then Formula.mk_and property phi
      else Formula.mk_neg @@ Formula.mk_imply property phi

  (* assume phi is nnf *)
  let rec defined_formula_of_aux (fenv : t) = function
    | Formula.Atom _ as phi -> defined_atom_formula_of true fenv phi
    | UnaryOp (Not, phi1, _) -> defined_atom_formula_of false fenv phi1
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp
          ( op,
            defined_formula_of_aux fenv phi1,
            defined_formula_of_aux fenv phi2,
            info )
    | Bind (binder, env, phi1, info) ->
        Bind (binder, env, defined_formula_of_aux fenv phi1, info)
    | LetRec (funcs, phi1, info) ->
        LetRec
          ( Formula.map_funcs ~f:(defined_formula_of_aux fenv) funcs,
            defined_formula_of_aux fenv phi1,
            info )
    | LetFormula (tvar, sort, def, body, info) ->
        LetFormula
          (tvar, sort, (*ToDo*) def, defined_formula_of_aux fenv body, info)

  let defined_formula_of (fenv : t) phi =
    if Map.Poly.is_empty fenv then phi
    else defined_formula_of_aux fenv @@ Formula.nnf_of phi

  let str_of t =
    String.concat_map_list ~sep:"\n" (Map.Poly.to_alist t)
      ~f:(fun (v, (params, _, def, is_rec, prop)) ->
        sprintf "%s %s %s = %s where %s"
          (if is_rec then "let rec" else "let")
          (Ident.name_of_tvar v)
          (String.concat_map_list ~sep:" " params ~f:(fun (x, s) ->
               sprintf "(%s:%s)" (Ident.name_of_tvar x) (Term.str_of_sort s)))
          (Term.str_of def) (Formula.str_of prop))
end

and DTEnv :
  (Type.DTEnvType
    with type flag := Datatype.flag
     and type datatype := Datatype.t
     and type dtfunc := Datatype.func
     and type formula := Formula.t) = struct
  type t = (string, Datatype.t) Map.Poly.t

  let mk_empty () = Map.Poly.empty
  let look_up_dt = Map.Poly.find

  let look_up_func t name =
    Map.Poly.fold t ~init:None ~f:(fun ~key:_ ~data:dt -> function
      | Some _ as ret -> ret
      | None -> (
          match Datatype.look_up_func dt name with
          | Some func -> Some (dt, func)
          | None -> None))

  let look_up_dt_by_cons_name t name =
    match look_up_func t name with Some (dt, _) -> Some dt | None -> None

  let name_is_cons t name =
    match look_up_func t name with
    | Some (_, func) -> Datatype.is_fcons func
    | _ -> false

  let name_is_sel t name =
    match look_up_func t name with
    | Some (_, func) -> Datatype.is_fsel func
    | _ -> false

  let name_is_func t name =
    match look_up_func t name with Some _ -> true | _ -> false

  let str_of t =
    String.concat_map_list ~sep:"\n" (Map.to_alist t) ~f:(snd >> Datatype.str_of)

  let update_dt t dt =
    let name = Datatype.name_of dt in
    match look_up_dt t name with
    | Some _ -> Map.Poly.set t ~key:name ~data:dt
    | None -> Map.Poly.add_exn t ~key:name ~data:dt

  let update_dts t dt =
    List.fold_left (Datatype.dts_of dt) ~init:t ~f:(fun env dt1 ->
        update_dt env @@ Datatype.update_name dt @@ Datatype.name_of_dt dt1)

  let force_merge env1 env2 = Map.force_merge env1 env2

  let rec of_sort = function
    | T_dt.SDT dt ->
        let params = Datatype.params_of dt in
        let full_name =
          Datatype.full_name_of (*adding instantiated datatypes?*) dt
        in
        force_merge (of_sorts params) @@ Map.Poly.singleton full_name dt
    | _ -> Map.Poly.empty

  and of_sorts =
    List.fold ~init:Map.Poly.empty ~f:(fun ret sort ->
        force_merge ret @@ of_sort sort)

  let rec of_term = function
    | Term.Var (_, T_dt.SDT dt, _) -> of_sort (T_dt.SDT dt)
    | Term.FunApp (T_dt.DTSel (_, dt, ret_sort), ts, _) ->
        of_sort (T_dt.SDT dt)
        |> force_merge (of_sort ret_sort)
        |> force_merge @@ of_terms ts
    | Term.FunApp (T_dt.DTCons (_, args, dt), ts, _) ->
        of_sort (T_dt.SDT dt)
        |> force_merge (of_sorts args)
        |> force_merge @@ of_terms ts
    | Term.FunApp (T_bool.Formula phi, _, _) -> of_formula phi
    | Term.FunApp (FVar (_, sargs, sret), ts, _) ->
        force_merge (of_sorts (sargs @ [ sret ])) (of_terms ts)
    | Term.FunApp (_, ts, _) as term ->
        force_merge (of_terms ts) @@ of_sort (Term.sort_of term)
    | _ -> Map.Poly.empty

  and of_terms =
    List.fold_left ~init:Map.Poly.empty ~f:(fun ret term ->
        force_merge ret @@ of_term term)

  and of_atom = function
    | Atom.App (Predicate.Psym (T_dt.IsCons (_, dt)), [ t ], _) ->
        force_merge (of_term t) @@ of_sort (T_dt.SDT dt)
    | Atom.App (_, ts, _) -> of_terms ts
    | _ -> Map.Poly.empty

  and of_formula phi =
    Formula.fold phi
      ~f:
        (object
           method fatom atom = of_atom atom
           method fnot r1 = r1
           method fand r1 r2 = force_merge r1 r2
           method for_ r1 r2 = force_merge r1 r2
           method fimply r1 r2 = force_merge r1 r2
           method fiff r1 r2 = force_merge r1 r2
           method fxor r1 r2 = force_merge r1 r2
           method fbind _ _ r1 = r1

           method fletrec funcs r1 =
             Map.force_merge_list
               (r1 :: List.map funcs ~f:(fun def -> def.Formula.body))

           method flet _ _ def body = force_merge body (of_term def)
        end)
end

and Rand :
  (Type.RandType
    with type formula := Formula.t
     and type term := Term.t
     and type termSubst := TermSubst.t) = struct
  type t =
    | Uniform of Term.t * Term.t
    | Gauss of Term.t * Term.t
    | IntUniform of Term.t * Term.t

  let mk_uniform t1 t2 = Uniform (t1, t2)
  let mk_gauss t1 t2 = Gauss (t1, t2)
  let mk_int_uniform t1 t2 = IntUniform (t1, t2)
  let let_uniform = function Uniform (t1, t2) -> (t1, t2) | _ -> assert false
  let let_gauss = function Gauss (t1, t2) -> (t1, t2) | _ -> assert false

  let let_int_uniform = function
    | IntUniform (t1, t2) -> (t1, t2)
    | _ -> assert false

  let subst map = function
    | Uniform (t1, t2) -> mk_uniform (Term.subst map t1) (Term.subst map t2)
    | Gauss (t1, t2) -> mk_gauss (Term.subst map t1) (Term.subst map t2)
    | IntUniform (t1, t2) ->
        mk_int_uniform (Term.subst map t1) (Term.subst map t2)

  let subst_sorts map = function
    | Uniform (t1, t2) ->
        Uniform (Term.subst_sorts map t1, Term.subst_sorts map t2)
    | Gauss (t1, t2) -> Gauss (Term.subst_sorts map t1, Term.subst_sorts map t2)
    | IntUniform (t1, t2) ->
        IntUniform (Term.subst_sorts map t1, Term.subst_sorts map t2)

  let subst_conts map = function
    | Uniform (t1, t2) ->
        Uniform (Term.subst_conts map t1, Term.subst_conts map t2)
    | Gauss (t1, t2) -> Gauss (Term.subst_conts map t1, Term.subst_conts map t2)
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
        sprintf "Uniform(%s, %s)" (Term.str_of t1) (Term.str_of t2)
    | Gauss (t1, t2) ->
        sprintf "Gauss(%s, %s)" (Term.str_of t1) (Term.str_of t2)
    | IntUniform (t1, t2) ->
        sprintf "IntUniform(%s, %s)" (Term.str_of t1) (Term.str_of t2)

  let rename map = function
    | Uniform (t1, t2) -> Uniform (Term.rename map t1, Term.rename map t2)
    | Gauss (t1, t2) -> Gauss (Term.rename map t1, Term.rename map t2)
    | IntUniform (t1, t2) -> IntUniform (Term.rename map t1, Term.rename map t2)

  (*Invariant: t1 <= t2*)
  let mk_uniform_bounds vars = function
    | Uniform (t1, t2) ->
        Formula.and_of @@ List.concat
        @@ List.map vars ~f:(fun var ->
               let t = Term.mk_var var T_real.SReal in
               [ Formula.leq t1 t; Formula.leq t t2 ])
    | IntUniform (t1, t2) ->
        Formula.and_of @@ List.concat
        @@ List.map vars ~f:(fun var ->
               let t = Term.mk_var var T_int.SInt in
               [ Formula.leq t1 t; Formula.leq t t2 ])
    | _ -> assert false
end

type model = (sort_bind * Term.t option) list

(*val str_of_model:  -> string*)
let str_of_model model =
  String.concat_map_list ~sep:", " model ~f:(function
    | (Ident.Tvar tvar, _), None -> sprintf "%s |-> *" tvar
    | (Ident.Tvar tvar, _), Some value ->
        sprintf "%s |-> %s" tvar (Term.str_of value))

module UTermEnv = struct
  type t = {
    term_to_tvar : (Term.t, Ident.tvar * Formula.t Set.Poly.t) Hashtbl.Poly.t;
    tvar_to_term : (Ident.tvar, Term.t * Formula.t Set.Poly.t) Hashtbl.Poly.t;
  }

  let create () : t =
    {
      term_to_tvar = Hashtbl.Poly.create ();
      tvar_to_term = Hashtbl.Poly.create ();
    }

  let clone t =
    {
      term_to_tvar = Hashtbl.Poly.copy t.term_to_tvar;
      tvar_to_term = Hashtbl.Poly.copy t.tvar_to_term;
    }

  let is_empty t = Hashtbl.Poly.is_empty t.term_to_tvar

  let set t term tvar constrs =
    Hashtbl.Poly.set t.term_to_tvar ~key:term ~data:(tvar, constrs);
    Hashtbl.Poly.set t.tvar_to_term ~key:tvar ~data:(term, constrs)

  let of_term t term =
    match Hashtbl.Poly.find t.term_to_tvar term with
    | Some (tvar, constrs) -> (tvar, constrs)
    | None ->
        let tvar = Ident.Tvar (sprintf "|%s|" (Term.str_of term)) in
        let constrs = Set.Poly.empty in
        set t term tvar constrs;
        (tvar, constrs)

  let of_tvar t = Hashtbl.Poly.find_exn t.tvar_to_term

  let add_constr_by_term t term phi =
    let tvar, constrs =
      match Hashtbl.Poly.find t.term_to_tvar term with
      | Some (tvar, constrs) -> (tvar, constrs)
      | None -> (Ident.Tvar (sprintf "|%s|" (Term.str_of term)), Set.Poly.empty)
    in
    let constrs' = Set.add constrs phi in
    set t term tvar constrs'

  let add_constr_by_tvar t tvar phi =
    let term, constrs = Hashtbl.Poly.find_exn t.tvar_to_term tvar in
    let constrs' = Set.add constrs phi in
    set t term tvar constrs'

  let update_by_model t (model : model) =
    List.iter model ~f:(function
      | (tvar, _), Some term -> (
          try
            let t1, _ = of_tvar t tvar in
            add_constr_by_tvar t tvar @@ Formula.eq t1 term
          with _ -> ())
      | (_, _), _ -> ())

  let to_sub t =
    Map.Poly.of_alist_exn @@ Hashtbl.Poly.to_alist
    @@ Hashtbl.Poly.map t.tvar_to_term ~f:fst

  (* assumed phi is simplifyed*)
  let subst_formula t phi =
    if is_empty t then phi
    else
      Formula.map_term phi ~f:(fun term ->
          if Term.is_uninterpreted_term term then
            Term.mk_var (fst @@ of_term t term) (Term.sort_of term)
          else term)

  let to_formula t =
    if is_empty t then Formula.mk_true ()
    else
      Formula.and_of @@ Set.to_list
      @@ Hashtbl.Poly.fold t.tvar_to_term ~init:Set.Poly.empty
           ~f:(fun ~key:_ ~data:(_, constrs) ret -> Set.union constrs ret)

  let to_neg_formula t =
    Formula.and_of @@ List.map ~f:Formula.mk_neg @@ Set.to_list
    @@ Hashtbl.Poly.fold t.tvar_to_term ~init:Set.Poly.empty
         ~f:(fun ~key:_ ~data:(_, constrs) ret -> Set.union constrs ret)

  let str_of t =
    Hashtbl.Poly.fold t.tvar_to_term ~init:""
      ~f:(fun ~key:tvar ~data:(term, constrs) ret ->
        sprintf "%s\n %s <=> %s :\n  %s" ret (Term.str_of term)
          (Ident.name_of_tvar tvar)
          (String.concat_map_set ~sep:"\n  " ~f:Formula.str_of constrs))
end

let remove_dontcare_elem ?(freshvar = false) ((x, s), v) =
  match v with
  | None ->
      ( x,
        if freshvar then
          Term.mk_var (Ident.mk_fresh_dontcare (Ident.name_of_tvar x)) s
        else Term.mk_dummy s )
  | Some t -> (x, t)

let remove_dontcare ?(freshvar = false) m =
  List.filter m ~f:(function
    | (Ident.Tvar "div0", Sort.SArrow (_, _)), None ->
        false (* bug of model generation of z3 4.8.8? *)
    | (Ident.Tvar "mod0", Sort.SArrow (_, _)), None ->
        false (* bug of model generation of z3 4.8.8? *)
    | (Ident.Tvar "array-ext", Sort.SArrow (_, _)), None -> false
    | _ -> true)
  |> List.map ~f:(remove_dontcare_elem ~freshvar)

let ref_dtenv = Atomic.make @@ DTEnv.mk_empty ()
let get_dtenv () = Atomic.get ref_dtenv
let set_dtenv = Atomic.set ref_dtenv

let update_dtenv (dtenv : DTEnv.t) =
  set_dtenv
  @@ Map.Poly.merge_skewed
       ~combine:(fun ~key:_ data1 _data2 -> data1)
       (*Map.force_merge
       ~catch_dup:(fun (name, t1, t2) ->
         if true then t1
         else
           failwith
           @@ sprintf "duplicate definition of %s as %s and %s" name
                (Datatype.str_of t1) (Datatype.str_of t2))*)
       dtenv
  @@ get_dtenv ()

let init_dtenv () =
  set_dtenv
    (DTEnv.mk_empty ()
    |> Map.Poly.add_exn ~key:"unit" ~data:(Datatype.mk_unit_dt ())
    |> Map.Poly.add_exn ~key:"option" ~data:(Datatype.mk_option_dt ())
    (* |> Map.Poly.add_exn ~key:"exn" ~data:(Datatype.mk_exn_dt ()) *)
    |> Map.Poly.add_exn ~key:"list" ~data:(Datatype.mk_list_dt ()))

let _ = init_dtenv ()
let ref_fenv = Atomic.make @@ FunEnv.mk_empty ()
let get_fenv () = Atomic.get ref_fenv
let set_fenv = Atomic.set ref_fenv

let update_fenv fenv =
  Map.Poly.iteri fenv ~f:(fun ~key ~data:_ -> Hash_set.add defined_fvars key);
  set_fenv @@ Map.force_merge fenv @@ get_fenv ()

let init_fenv () = set_fenv @@ FunEnv.mk_empty ()

type term_subst_elem = Ident.tvar * Term.t
type term_subst_set = term_subst_elem Set.Poly.t
type term_subst_list = term_subst_elem list
type term_subst_map = (Ident.tvar, Term.t) Map.Poly.t
type func_subst_elem = Ident.tvar * (sort_env_list * Term.t)
type func_subst_set = func_subst_elem Set.Poly.t
type func_subst_list = func_subst_elem list
type func_subst_map = FuncSubst.t
type pred_subst_elem = Ident.pvar * (sort_env_list * Formula.t)
type pred_subst_set = pred_subst_elem Set.Poly.t
type pred_subst_list = pred_subst_elem list
type pred_subst_map = PredSubst.t
