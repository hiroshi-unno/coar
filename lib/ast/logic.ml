(* The higher-order term language: simply typed lambda terms with
   polymorphism ([TyApp], [TyLam]) and effect-annotated arrow sorts, in which
   constants, formulas, predicates and candidate solutions are all terms.
   The constraint solver's clauses, templates and candidate solutions live
   here; the parsers, the frontends and the solver interface use the
   first-order language [LogicOld].  The two are both load-bearing and are
   converted with [ExtTerm.of_old_*] and [ExtTerm.to_old_*]; the latter take
   two sort environments, the unknowns' and then the ordinary variables',
   and exchanging them is not a type error.

   Symbols ([sym]), sorts and literals are extensible variants: each theory
   module ([BoolTerm], [IntTerm], ..., [RegexTerm]) adds its constructors and
   [ExtTerm] includes them all, so a match on them can never be exhaustive
   and a new symbol fails at run time in every consumer that does not know
   it.

   Binding forms are [Bin] (lambda, the quantifiers and the fixpoint
   binders) and [Let].  [Term.subst] is capture-avoiding -- it renames every
   binder it passes, drawing fresh names from the global counter -- and
   simultaneous, and beta-reduces the redexes the substitution creates;
   [rename] is not capture-avoiding.  The faster forms beside it
   ([subst_sharing], [subst_up_to_bound_names], [subst_rename_on_capture])
   state, each in its own comment, how their result relates to [subst]'s.
   [fvs_of] counts neither a name of the process-global function
   environment nor a registered dummy term as free. *)
open Core
open Common.Ext
open Common.Util
open Common.Combinator

module Sort = struct
  type t = ..
  and e = ..
  and o = ..

  type c = { op_sig : o; val_type : t; cont_eff : e }
  type t += SVar of Ident.svar | SArrow of t * c | SForAll of Ident.svar * t
  type e += EVar of Ident.evar | Pure | Eff of c * c

  type o +=
    | OpSig of
        (string, t) ALMap.t
        * Ident.rvar option (* Some r: open / None: closed *)

  let empty_closed_opsig = OpSig (ALMap.empty, None)

  let is_empty_closed_opsig = function
    | OpSig (map, None) -> ALMap.is_empty map
    | _ -> false

  let is_empty_opsig = function
    | OpSig (map, _) -> ALMap.is_empty map
    | _ -> false

  let is_pure = function Pure -> true | _ -> false
  let is_eff = function Eff _ -> true | _ -> false
  let is_pure_triple c = is_pure c.cont_eff && is_empty_opsig c.op_sig
  let mk_cont_eff c1 c2 = Eff (c1, c2)
  let mk_fresh_svar () = SVar (Ident.mk_fresh_svar ())

  let mk_arrow ?(opsig = empty_closed_opsig) ?(cont = Pure) s1 s2 =
    SArrow (s1, { op_sig = opsig; val_type = s2; cont_eff = cont })

  let rec mk_fun = function
    | [ s ] -> s
    | s :: ss -> mk_arrow s (mk_fun ss)
    | _ -> assert false

  let mk_forall v sort = SForAll (v, sort)
  let is_arrow = function SArrow _ -> true | _ -> false

  let rec arity_of = function
    | SVar _ -> assert false
    | SArrow (_s, c) -> 1 + arity_of c.val_type
    | SForAll (_, s) -> arity_of s
    | _ -> 0 (* assert false*)

  let rec ret_of = function SArrow (_s, c) -> ret_of c.val_type | sort -> sort

  let rec args_of = function
    | SArrow (s, c) -> s :: args_of c.val_type
    | _ -> []

  let rec args_ret_of = function
    | SArrow (s, c) ->
        let args, ret = args_ret_of c.val_type in
        (s :: args, ret)
    | s -> ([], s)
end

type sort_bind = Ident.tvar * Sort.t
type sort_env_set = sort_bind Set.Poly.t
type sort_env_list = sort_bind list
type sort_env_map = (Ident.tvar, Sort.t) Map.Poly.t

(* Whether a failed variable lookup in [ExtTerm.to_old_*] prints the
   environments it searched (to stderr) before raising.  Off by default: some
   callers catch that failure as an ordinary outcome and retry, so the dump
   would flood a normal run's stderr; solvers turn it on when their
   configuration is verbose. *)
let print_unbound_envs = Atomic.make false

let mk_fresh_sort_env_list : Sort.t list -> sort_env_list =
  List.map ~f:(fun sort -> (Ident.mk_fresh_tvar (), sort))

let sort_env_list_of_sorts ?(pre = "") sorts =
  let param_ident_count = ref 0 in
  let mk_param_ident () =
    incr param_ident_count;
    Ident.Tvar (pre ^ "x" ^ string_of_int !param_ident_count)
  in
  List.map sorts ~f:(fun sort -> (mk_param_ident (), sort))

let str_of_sort_env_list str_of_sort =
  String.concat_map_list ~sep:" " ~f:(fun (tvar, sort) ->
      String.paren
      @@ sprintf "%s: %s" (Ident.name_of_tvar tvar) (str_of_sort sort))

let str_of_sort_env_map str_of_sort =
  Map.Poly.to_alist >> str_of_sort_env_list str_of_sort

let str_of_term_subst str_of_term =
  Map.Poly.to_alist
  >> String.concat_map_list ~sep:"\n" ~f:(fun (tvar, term) ->
      sprintf "%s |-> %s" (Ident.name_of_tvar tvar) (str_of_term term))

type sym = ..
type termlit = ..
type termlit += FunLit of (termlit -> termlit) | SFunLit of (Sort.t -> termlit)
type info = ..
type info += Dummy
(*type info += ID of int*)

type binder = Mu | Nu | Fix | Lambda | Forall | Exists

type term =
  | Var of Ident.tvar * info
  | Con of sym * info
  | App of term * term * info
  | Bin of binder * Ident.tvar * Sort.t * term * info
  | Let of Ident.tvar * Sort.t * term * term * info
  | TyApp of term * Sort.t * info
  | TyLam of Ident.svar * term * info

type term_bind = Ident.tvar * term
type term_subst_set = term_bind Set.Poly.t
type term_subst_list = term_bind list
type term_subst_map = (Ident.tvar, term) Map.Poly.t
type pred_subst_set = (sort_bind * term) Set.Poly.t
type pred_subst_list = (sort_bind * term) list
type pred_subst_map = (sort_bind, term) Map.Poly.t
type cand_map = (Ident.tvar, Sort.t * term) Map.Poly.t
type cand_list = (Ident.tvar * (Sort.t * term)) list
type model_elem = sort_bind * term option
type model = model_elem list

(* [first_binding_table model] maps each variable bound in [model] to the
   first element of [model] that binds it.  Contract: for every [x],
   [Hashtbl.find (first_binding_table model) x] equals
   [List.find model ~f:(fun ((y, _), _) -> Stdlib.( = ) y x)] -- [Hashtbl.add]
   never replaces an existing key, so a later duplicate binding is ignored as
   [List.find] ignores it, and the table's polymorphic equality on a variable
   (a string under one constructor) is [Stdlib.( = )].  Built in one pass, so
   a lookup per variable costs a hash rather than a scan of the model. *)
let first_binding_table (model : model) : (Ident.tvar, model_elem) Hashtbl.t =
  let tbl = Hashtbl.Poly.create ~size:(List.length model) () in
  List.iter model ~f:(fun (((x, _), _) as elem) ->
      ignore (Hashtbl.add tbl ~key:x ~data:elem : [ `Ok | `Duplicate ]));
  tbl

module type TermType = sig
  (** Sorts *)

  val open_arity_of_sym : (sym -> Sort.t) -> sym -> int

  val open_sort_of :
    (sym -> Sort.t) ->
    (Ident.svar * Sort.t -> Sort.t -> Sort.t) ->
    sort_env_map ->
    term ->
    Sort.t

  val open_head_sort_of :
    (sym -> Sort.t) ->
    (Ident.svar * Sort.t -> Sort.t -> Sort.t) ->
    sort_env_map ->
    term ->
    Sort.t
  (** [open_head_sort_of] returns what [open_sort_of] returns on every term it
      returns a sort for, reading only the spine: an application's argument and
      a [let]'s definition are not visited, since neither decides the result.
      Where [open_sort_of] raises because of such a subterm, this returns. *)

  val sym_sort_map : (sym, Sort.t) Map.Poly.t
  val arity_of_sym : sym -> int
  val sort_of_sym : sym -> Sort.t

  (** Printing *)

  val open_str_of_sort : (Sort.t -> string) -> Sort.t -> string
  val open_is_acompound : (Sort.t -> bool) -> Sort.t -> bool

  val open_str_of_sort_acompound :
    (Sort.t -> bool) -> (Sort.t -> string) -> Sort.t -> string
  val open_str_of : (Sort.t -> string) -> (sym -> string) -> term -> string
  val str_of_sym : sym -> string
  val str_of_termlit : termlit -> string
  val str_of_sort : Sort.t -> string
  val str_of : term -> string

  (** Construction *)

  val mk_var : Ident.tvar -> term
  val mk_con : sym -> term
  val mk_app : term -> term -> term
  val mk_apps : term -> term list -> term
  val mk_sym_app : sym -> term list -> term
  val mk_var_app : Ident.tvar -> term list -> term
  val mk_bind : binder -> Ident.tvar -> Sort.t -> term -> term
  val mk_binds : binder -> sort_env_list -> term -> term
  val mk_mixed_binds : (binder * Ident.tvar * Sort.t) list -> term -> term
  val let_quants : term -> (binder * Ident.tvar * Sort.t) list * term
  val num_binds : term -> int
  val mk_let : Ident.tvar -> Sort.t -> term -> term -> term
  val mk_tyapp : term -> Sort.t -> term
  val mk_tylam : Ident.svar -> term -> term
  val mk_lambda : sort_env_list -> term -> term

  (** Destruction *)

  val let_var : term -> Ident.tvar * info
  val let_con : term -> sym * info
  val let_app : term -> term * term * info
  val let_apps : term -> term * term list
  val let_sym_app : term -> sym * term list
  val let_var_app : term -> Ident.tvar * term list
  val let_bin : term -> binder * Ident.tvar * Sort.t * term * info
  val let_let : term -> Ident.tvar * Sort.t * term * term * info
  val let_tyapp : term -> term * Sort.t * info
  val let_tylam : term -> Ident.svar * term * info
  val let_lam : term -> sort_env_list * term

  (** Substitution *)

  val rename : Ident.tvar_map -> term -> term

  val subst :
    ?beta_red:bool -> term_subst_map -> ?next:(term -> term) -> term -> term

  val beta_reduction : ?next:(term -> term) -> term -> term
  val refresh : sort_env_map * term -> sort_env_map * term
  val unify : term -> term -> term_subst_map option

  (** Evaluation *)

  val open_assert_sort_check :
    (Sort.t -> termlit -> unit) -> Sort.t -> termlit -> unit

  val open_eval :
    (sym -> termlit) ->
    (termlit -> term) ->
    (sym, Sort.t) Map.Poly.t ->
    term ->
    termlit

  val is_termlit : termlit -> bool
  val of_termlit : termlit -> term
  val assert_sort_check : Sort.t -> termlit -> unit
  val eval_sym : sym -> termlit
  val eval : (sym, Sort.t) Map.Poly.t -> term -> termlit

  (** Observation *)

  val is_var : term -> bool
  val is_con : term -> bool
  val is_app : term -> bool
  val is_lam : term -> bool
  val is_bin : term -> bool
  val is_let : term -> bool
  val is_tyapp : term -> bool
  val is_tylam : term -> bool
  val is_var_app : term -> bool

  val svs_of :
    (sym -> Ident.svar_set) ->
    (Sort.t -> Ident.svar_set) ->
    term ->
    Ident.svar_set

  val occurs_free : Ident.tvar -> term -> bool
  val subst_sharing : (Ident.tvar, term) Map.Poly.t -> term -> term
  val subst_up_to_bound_names : term_subst_map -> term -> term
  val subst_rename_on_capture : term_subst_map -> term -> term
  val subst_up_to_bound_names_linear : term_subst_map -> term -> term
  val fvs_of : term -> Ident.tvar_set

  val fvs_of_shared : unit -> term -> Ident.tvar_set
  (** [fvs_of_shared ()] is [fvs_of] remembering each node's set by physical
      identity while the returned function lives *)

  val find : f:(term -> bool) -> term -> term option
  val pvar_of_atom : term -> Ident.tvar
  val ast_size : term -> int
  val ast_size_up_to : int -> term -> int

  val let_sort_env_of :
    term ->
    (Ident.tvar, Sort.t, Comparator.Poly.comparator_witness) Map.Poly.map

  val let_env_of : ?map:term_subst_map -> term -> term_subst_map

  (** Transformation *)

  val reduce_sort_map : sort_env_map * term -> sort_env_map * term
end

module Term : TermType = struct
  (** Sorts *)

  let open_arity_of_sym sort_of_sym sym = Sort.arity_of @@ sort_of_sym sym

  let rec open_sort_of sort_of_sym subst_sort var_env = function
    | Var (v, _) -> (
        try Map.Poly.find_exn var_env v
        with exn_ when not (Common.Timer.is_async exn_) ->
          failwith @@ Ident.name_of_tvar v ^ " not found")
    | Con (sym, _) -> sort_of_sym sym
    | App (t1, t2, _) -> (
        match
          ( open_sort_of sort_of_sym subst_sort var_env t1,
            open_sort_of sort_of_sym subst_sort var_env t2 )
        with
        | Sort.SArrow (s11, c), s2 when Sort.is_pure_triple c ->
            if Stdlib.(s11 = s2) then c.val_type else (*ToDo*) c.val_type
        | _ -> failwith "The sort of App is unmached")
    | Bin (bind, tvar, sort, term, _) -> (
        match bind with
        | Lambda ->
            let new_var_env = Map.Poly.add_exn var_env ~key:tvar ~data:sort in
            open_sort_of sort_of_sym subst_sort new_var_env term
        | _ -> failwith "The sort of Bin is not implemented yet")
    | Let (v, sort, t1, t2, _) ->
        if not Stdlib.(sort = open_sort_of sort_of_sym subst_sort var_env t1)
        then failwith "The sort of let-expression is wrong"
        else
          let new_var_env = Map.Poly.add_exn var_env ~key:v ~data:sort in
          open_sort_of sort_of_sym subst_sort new_var_env t2
    | TyApp (term, sort, _) -> (
        match term with
        | Con (sym, _) -> (
            match sort_of_sym sym with
            | Sort.SForAll (svar, s1) -> subst_sort (svar, sort) s1
            | _ -> failwith "TyApp can be used only for SForAll")
        | TyApp _ -> failwith "it is not implemented yet"
        | TyLam _ -> failwith "it is not implemented yet"
        | _ -> failwith "The sort of term cannot apply another sort")
    | TyLam _ -> failwith "it is not implemented yet"

  (* The sort of an application is the result sort of its function's sort,
     whatever the argument's sort is ([open_sort_of] computes the argument's
     sort and then returns [c.val_type] on both branches of its comparison),
     and a [let]'s sort is its body's.  So the spine decides the sort, and a
     caller that only needs the sort of a large term -- the conversion asks it
     at every [ite] and [case] node, of a whole branch -- need not walk the
     arguments, nor compare their sorts structurally at each application. *)
  let rec open_head_sort_of sort_of_sym subst_sort var_env = function
    | App (t1, _, _) -> (
        match open_head_sort_of sort_of_sym subst_sort var_env t1 with
        | Sort.SArrow (_, c) when Sort.is_pure_triple c -> c.val_type
        | _ -> failwith "The sort of App is unmached")
    | Bin (Lambda, tvar, sort, term, _) ->
        let new_var_env = Map.Poly.add_exn var_env ~key:tvar ~data:sort in
        open_head_sort_of sort_of_sym subst_sort new_var_env term
    | Let (v, sort, _, t2, _) ->
        let new_var_env = Map.Poly.add_exn var_env ~key:v ~data:sort in
        open_head_sort_of sort_of_sym subst_sort new_var_env t2
    | term -> open_sort_of sort_of_sym subst_sort var_env term

  let sym_sort_map = Map.Poly.empty
  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = open_arity_of_sym sort_of_sym

  (** Printing *)

  let str_of_binder = function
    | Mu -> "Mu"
    | Nu -> "Nu"
    | Fix -> "Fix"
    | Lambda -> "Lam"
    | Forall -> "forall"
    | Exists -> "exists"

  let rec open_str_of str_of_sort str_of_sym = function
    | Var (Ident.Tvar id, _) -> String.paren id
    | Con (sym, _) -> String.paren (str_of_sym sym)
    | App (t1, t2, _) ->
        String.paren
        @@ sprintf "%s, %s"
             (open_str_of str_of_sort str_of_sym t1)
             (open_str_of str_of_sort str_of_sym t2)
    | Bin (bind, Ident.Tvar id, sort, t1, _) ->
        sprintf "%s %s:%s. (%s)" (str_of_binder bind) id (str_of_sort sort)
          (open_str_of str_of_sort str_of_sym t1)
    | Let (Ident.Tvar id, sort, t1, t2, _) ->
        sprintf "Let %s:%s = %s (%s)" id (str_of_sort sort)
          (open_str_of str_of_sort str_of_sym t1)
          (open_str_of str_of_sort str_of_sym t2)
    | TyApp (term, sort, _) ->
        sprintf "%s[%s]"
          (String.paren @@ open_str_of str_of_sort str_of_sym term)
          (str_of_sort sort)
    | TyLam (Ident.Svar s, term, _) ->
        sprintf "%s. %s" s
          (String.paren @@ open_str_of str_of_sort str_of_sym term)

  let rec open_str_of_sort str_of_sort = function
    | Sort.SVar (Ident.Svar s) -> s
    | Sort.SArrow (s, c) ->
        sprintf "(%s) -> %s%s%s"
          (open_str_of_sort str_of_sort s)
          (if Sort.is_empty_opsig c.op_sig then "" else "_ |> ")
          (open_str_of_sort str_of_sort c.val_type)
          (if Sort.is_pure c.cont_eff then "" else " / _")
    | Sort.SForAll (Ident.Svar v, s) ->
        String.paren
        @@ sprintf "forall %s. %s" v (open_str_of_sort str_of_sort s)
    | sort -> str_of_sort sort

  (* The parameterised form of the printer above: [is_acompound] says which
     sorts have to be parenthesised when they appear inside a compound one, so a
     theory can decide that -- an array, say -- without this function knowing
     about it.  Preserved beside the printer rather than replacing it, since
     every caller of that one passes no predicate. *)
  let open_is_acompound is_acompound = function
    | Sort.SVar _ -> false
    | Sort.SArrow (_, _) | Sort.SForAll (_, _) -> true
    | sort -> is_acompound sort

  (* Sort printing parameterised by which sorts need parentheses as an
     argument. Added for the array work; the existing printers are untouched
     and nothing uses this yet. *)
  let rec open_str_of_sort_acompound is_acompound str_of_sort sort =
    let paren s =
      if open_is_acompound is_acompound sort then String.paren s else s
    in
    match sort with
    | Sort.SVar (Ident.Svar s) -> s
    | Sort.SArrow (s, c) ->
        paren
        @@ sprintf "(%s) -> %s%s%s"
             (open_str_of_sort_acompound is_acompound str_of_sort s)
             (if Sort.is_empty_opsig c.op_sig then "" else "_ |> ")
             (open_str_of_sort_acompound is_acompound str_of_sort c.val_type)
             (if Sort.is_pure c.cont_eff then "" else " / _")
    | Sort.SForAll (Ident.Svar v, s) ->
        String.paren
        @@ sprintf "forall %s. %s" v
             (open_str_of_sort_acompound is_acompound str_of_sort s)
    | sort -> paren (str_of_sort sort)

  let str_of_sym _ = failwith "Term.str_of_sym"
  let str_of_termlit _ = failwith "Term.str_of_termlit"
  let str_of_sort _ = failwith "Term.str_of_sort"
  let str_of = open_str_of str_of_sort str_of_sym

  (** Construction *)

  let info_id_count = ref 0

  (*let get_info_id () = incr info_id_count; !info_id_count*)
  let mk_var var =
    incr info_id_count;
    Var (var, Dummy (*ID (get_info_id ())*))

  let mk_con sym =
    incr info_id_count;
    Con (sym, Dummy (*ID (get_info_id ())*))

  let mk_app t1 t2 =
    incr info_id_count;
    App (t1, t2, Dummy (*ID (get_info_id ())*))

  let mk_apps t ts = List.fold ~f:mk_app ~init:t ts
  let mk_sym_app sym args = mk_apps (mk_con sym) args
  let mk_var_app var args = mk_apps (mk_var var) args

  let mk_bind bind var sort term =
    incr info_id_count;
    Bin (bind, var, sort, term, Dummy (*ID (get_info_id ())*))

  let mk_let var sort t1 t2 =
    incr info_id_count;
    Let (var, sort, t1, t2, Dummy (*ID (get_info_id ())*))

  let mk_tyapp term sort =
    incr info_id_count;
    TyApp (term, sort, Dummy (*ID (get_info_id ())*))

  let mk_tylam svar term =
    incr info_id_count;
    TyLam (svar, term, Dummy (*ID (get_info_id ())*))

  let mk_lambda args term =
    List.fold_right args ~init:term ~f:(Tuple2.uncurry @@ mk_bind Lambda)

  (** Destruction *)

  let let_var = function Var (var, info) -> (var, info) | _ -> assert false
  let let_con = function Con (sym, info) -> (sym, info) | _ -> assert false

  let let_app = function
    | App (t1, t2, info) -> (t1, t2, info)
    | _ -> assert false

  let rec let_apps = function
    | App (t1, t2, _) ->
        let t, ts = let_apps t1 in
        (t, ts @ [ t2 ])
    | t -> (t, [])

  let let_sym_app t =
    let t, ts = let_apps t in
    match t with Con (sym, _) -> (sym, ts) | _ -> assert false

  let let_var_app t =
    let t, ts = let_apps t in
    match t with Var (x, _) -> (x, ts) | _ -> assert false

  let let_bin = function
    | Bin (bind, var, sort, term, info) -> (bind, var, sort, term, info)
    | _ -> assert false

  let let_let = function
    | Let (var, sort, t1, t2, info) -> (var, sort, t1, t2, info)
    | _ -> assert false

  let let_tyapp = function
    | TyApp (term, sort, info) -> (term, sort, info)
    | _ -> assert false

  let let_tylam = function
    | TyLam (svar, term, info) -> (svar, term, info)
    | _ -> assert false

  let let_lam =
    let rec aux args = function
      | Bin (Lambda, tvar, sort, term, _) -> aux ((tvar, sort) :: args) term
      | term -> (List.rev args, term)
    in
    aux []

  (* The quantifier prefix, outermost first, and the body under it -- the
     analogue of [let_lam] for [Forall] and [Exists].  A term that is a lambda
     abstraction over a quantified body is taken apart by the two in turn. *)
  let let_quants =
    let rec aux args = function
      | Bin (((Forall | Exists) as b), tvar, sort, term, _) ->
          aux ((b, tvar, sort) :: args) term
      | term -> (List.rev args, term)
    in
    aux []

  (* How many binders of any kind a term begins with. *)
  let rec num_binds = function Bin (_, _, _, t, _) -> 1 + num_binds t | _ -> 0

  (** Observation *)

  let is_var = function Var (_, _) -> true | _ -> false
  let is_con = function Con (_, _) -> true | _ -> false
  let is_app = function App (_, _, _) -> true | _ -> false
  let is_lam = function Bin (Lambda, _, _, _, _) -> true | _ -> false
  let is_bin = function Bin (_, _, _, _, _) -> true | _ -> false
  let is_let = function Let (_, _, _, _, _) -> true | _ -> false
  let is_tyapp = function TyApp (_, _, _) -> true | _ -> false
  let is_tylam = function TyLam (_, _, _) -> true | _ -> false

  let rec is_var_app = function
    | Var (_, _) -> true
    | App (t, _, _) -> is_var_app t
    | _ -> false

  let svs_of svs_of_sym svs_of_sort term =
    let rec aux ~next = function
      | Var (_, _) -> next Set.Poly.empty
      | Con (sym, _) -> next @@ svs_of_sym sym
      | App (t1, t2, _) ->
          aux t1 ~next:(fun svs1 ->
              aux t2 ~next:(fun svs2 -> next @@ Set.union svs1 svs2))
      | Bin (_, _, sort, t1, _) ->
          aux t1 ~next:(fun svs ->
              next @@ Set.Poly.union_list [ svs; svs_of_sort sort ])
      | Let (_, sort, t1, t2, _) ->
          aux t1 ~next:(fun svs1 ->
              aux t2 ~next:(fun svs2 ->
                  next @@ Set.Poly.union_list [ svs1; svs2; svs_of_sort sort ]))
      | TyApp (term, _, _) | TyLam (_, term, _) -> aux term ~next
    in
    aux term ~next:Fn.id

  (* Does [x] occur free in [term]?  [Set.mem (fvs_of t) x] answers the same
     question by building the whole set first; this stops at the first
     occurrence and allocates nothing, which matters where the question is
     asked once per term per elimination round. *)
  let rec occurs_free x = function
    | Var (var, _) ->
        Stdlib.(var = x)
        && (not (LogicOld.is_dummy_term var None))
        && (not @@ Map.Poly.mem (LogicOld.get_fenv ()) var)
    | Con (_, _) -> false
    | App (t1, t2, _) -> occurs_free x t1 || occurs_free x t2
    | Bin (_, var, _, t, _) -> Stdlib.(var <> x) && occurs_free x t
    | Let (var, _, t1, t2, _) ->
        occurs_free x t1 || (Stdlib.(var <> x) && occurs_free x t2)
    | TyApp (t, _, _) | TyLam (_, t, _) -> occurs_free x t

  let fvs_of term =
    let rec aux ~next = function
      | Var (var, _) ->
          if
            LogicOld.is_dummy_term var None
            || Map.Poly.mem (LogicOld.get_fenv ()) var
          then next Set.Poly.empty
          else next @@ Set.Poly.singleton var
      | Con (_, _) -> next Set.Poly.empty
      | App (t1, t2, _) ->
          aux t1 ~next:(fun fvs1 ->
              aux t2 ~next:(fun fvs2 -> next @@ Set.union fvs1 fvs2))
      | Bin (_, var, _, t1, _) ->
          aux t1 ~next:(fun fvs -> next @@ Set.remove fvs var)
      | Let (var, _, t1, t2, _) ->
          aux t1 ~next:(fun fvs1 ->
              aux t2 ~next:(fun fvs2 ->
                  next @@ Set.remove (Set.union fvs1 fvs2) var))
      | TyApp (term, _, _) | TyLam (_, term, _) -> aux term ~next
    in
    aux term ~next:Fn.id

  (* [fvs_of_shared ()] is a function [fv] with [Set.mem (fv t) x] iff
     [Set.mem (fvs_of t) x] for every [t] and [x] (the same sets, as sets:
     built by the same unions and removals in the same order), which
     remembers the set of every application, binder and [let] node it reads by
     physical identity for as long as [fv] lives, so a term that shares
     subterms is read once per physical node rather than once per path.  It
     reads the function environment and the dummy terms as [fvs_of] does,
     and assumes neither changes while [fv] is in use. *)
  let fvs_of_shared () =
    let module Tbl = Stdlib.Hashtbl.Make (struct
      type t = term

      let equal = phys_equal
      let hash = Common.Ext.Hashtbl.phys_hash
    end) in
    let tbl = Tbl.create 1024 in
    let rec aux ~next t =
      match t with
      | Var (var, _) ->
          if
            LogicOld.is_dummy_term var None
            || Map.Poly.mem (LogicOld.get_fenv ()) var
          then next Set.Poly.empty
          else next @@ Set.Poly.singleton var
      | Con (_, _) -> next Set.Poly.empty
      | TyApp (term, _, _) | TyLam (_, term, _) -> aux term ~next
      | App _ | Bin _ | Let _ -> (
          match Tbl.find_opt tbl t with
          | Some s -> next s
          | None ->
              let next s =
                Tbl.replace tbl t s;
                next s
              in
              match t with
              | App (t1, t2, _) ->
                  aux t1 ~next:(fun fvs1 ->
                      aux t2 ~next:(fun fvs2 -> next @@ Set.union fvs1 fvs2))
              | Bin (_, var, _, t1, _) ->
                  aux t1 ~next:(fun fvs -> next @@ Set.remove fvs var)
              | Let (var, _, t1, t2, _) ->
                  aux t1 ~next:(fun fvs1 ->
                      aux t2 ~next:(fun fvs2 ->
                          next @@ Set.remove (Set.union fvs1 fvs2) var))
              | _ -> assert false)
    in
    fun t -> aux t ~next:Fn.id

  let rec find ~f t =
    if f t then Some t
    else
      match t with
      | Var (_, _) | Con (_, _) -> None
      | App (t1, t2, _) | Let (_, _, t1, t2, _) -> (
          match find ~f t1 with Some t -> Some t | None -> find ~f t2)
      | Bin (_, _, _, t1, _) | TyApp (t1, _, _) | TyLam (_, t1, _) -> find ~f t1

  let rec pvar_of_atom = function
    | Var (tvar, _) -> tvar
    | App (t, _, _) -> pvar_of_atom t
    | _ -> assert false

  let rec ast_size = function
    | Var (_, _) | Con (_, _) -> 1
    | App (t1, t2, _) | Let (_, _, t1, t2, _) -> 1 + ast_size t1 + ast_size t2
    | Bin (_, _, _, term, _) | TyApp (term, _, _) | TyLam (_, term, _) ->
        1 + ast_size term

  (* [ast_size_up_to cap t] is [min (ast_size t) (cap + 1)], computed in time
     proportional to its result rather than to [t]'s size.  [ast_size] counts
     the term as a tree, and a term built by substituting a definition into
     another one shares the substituted subterm physically wherever the
     variable occurred, so a chain of such definitions is small in memory
     while its tree -- which every traversal here walks, conversion and
     substitution included -- doubles with each link; asking [ast_size] of
     such a term costs what the traversal it is meant to guard would. *)
  let ast_size_up_to cap t =
    let exception Over in
    let n = ref 0 in
    let rec go t =
      incr n;
      if !n > cap then raise Over;
      match t with
      | Var _ | Con _ -> ()
      | App (t1, t2, _) | Let (_, _, t1, t2, _) ->
          go t1;
          go t2
      | Bin (_, _, _, t1, _) | TyApp (t1, _, _) | TyLam (_, t1, _) -> go t1
    in
    try
      go t;
      !n
    with Over -> cap + 1

  (** Construction *)

  (* [mk_binds] with the binder chosen per variable, and WITHOUT dropping the
     ones the body does not mention: a caller rebuilding a prefix it has just
     taken apart wants the binders it took, not the used ones. *)
  let mk_mixed_binds bounds body =
    List.fold_right bounds ~init:body ~f:(fun (binder, tvar, sort) acc ->
        mk_bind binder tvar sort acc)

  let mk_binds binder bounds body =
    let ftv = fvs_of body in
    List.filter bounds ~f:(fst >> Set.mem ftv)
    |> List.fold_right ~init:body ~f:(Tuple2.uncurry (mk_bind binder))

  (** Substitution *)

  let rec rename map = function
    | Var (var, info) -> (
        match Map.Poly.find map var with
        | None -> Var (var, info)
        | Some var' -> mk_var var')
    | Con (_, _) as c -> c
    | App (t1, t2, info) -> App (rename map t1, rename map t2, info)
    | Bin (bind, var, sort, term, info) ->
        Bin (bind, var, sort, rename (Map.Poly.remove map var) term, info)
    | Let (var, sort, t1, t2, info) ->
        Let (var, sort, rename map t1, rename (Map.Poly.remove map var) t2, info)
    | TyApp (term, sort, info) -> TyApp (rename map term, sort, info)
    | TyLam (svar, term, info) -> TyLam (svar, rename map term, info)

  let rec subst ?(beta_red = true) env ?(next = Fn.id) = function
    | Var (var, info) -> (
        next
        @@
        match Map.Poly.find env var with
        | None -> Var (var, info)
        | Some t -> t)
    | Bin (bind, var, sort, term, info) ->
        let var' = Ident.mk_fresh_tvar () in
        subst ~beta_red env
          (rename (Map.Poly.singleton var var') term)
          ~next:(fun t -> next @@ Bin (bind, var', sort, t, info))
    | Let (var, sort, t1, t2, info) ->
        subst ~beta_red env t1 ~next:(fun t1 ->
            let var' = Ident.mk_fresh_tvar () in
            subst ~beta_red env
              (rename (Map.Poly.singleton var var') t2)
              ~next:(fun t2 -> next @@ Let (var', sort, t1, t2, info)))
    | App (t1, t2, info) ->
        subst ~beta_red env t1 ~next:(fun t1 ->
            subst ~beta_red env t2 ~next:(fun t2 ->
                (if beta_red then beta_reduction ~next else next)
                @@ App (t1, t2, info)))
    | TyApp (term, sort, info) ->
        subst ~beta_red env term ~next:(fun t -> next @@ TyApp (t, sort, info))
    | TyLam (svar, term, info) ->
        subst ~beta_red env term ~next:(fun t -> next @@ TyLam (svar, t, info))
    | t -> next t

  and beta_reduction ?(next = Fn.id) = function
    | App (fn, arg, info) ->
        beta_reduction fn ~next:(function
          | Bin (Lambda, var, _sort, term', _) ->
              subst (Map.Poly.singleton var arg) term' ~next
          | t -> next @@ App (t, arg, info))
    | t -> next t

  (* [subst] rebuilds every node it passes and renames every binder, which costs
     a traversal and a fresh name even where the substitution cannot apply.  This
     one returns the subtree it was given, physically, wherever the substituted
     variables do not occur free in it; the subtrees it does enter are handed to
     [subst] itself, so the capture-avoidance and the beta-reduction there are
     unchanged.  Skipping a subtree also skips the beta-reduction [subst] would
     have performed inside it -- a substitution that applies nowhere still reduces
     redexes today -- so this is not a drop-in for every caller, and the one it
     was written for holds the result for its next round, where the preserved
     sharing is what pays. *)
  let rec subst_sharing env t =
    match t with
    | Var (var, _) -> (
        match Map.Poly.find env var with Some u -> u | None -> t)
    | Con _ -> t
    | App (t1, t2, info) ->
        let t1' = subst_sharing env t1 in
        let t2' = subst_sharing env t2 in
        if phys_equal t1 t1' && phys_equal t2 t2' then t
        else beta_reduction @@ App (t1', t2', info)
    | Bin _ | Let _ | TyApp _ | TyLam _ ->
        (* a binder is handed to [subst], which renames it and avoids capture;
           the test that decides whether to is the only place a free-variable set
           is built, and it is built once for the whole subtree rather than at
           every node of it *)
        if Set.are_disjoint (Map.key_set env) (fvs_of t) then t else subst env t

  (* [subst env t] up to the names of bound variables, for an [env] of
     lambda terms substituted into a beta-normal [t] -- the shape a template
     hole map has.

     Contract: where [t] is beta-normal and no variable of [env] occurs in the
     function position of an application whose result is applied again, the
     result is alpha-equivalent to [subst env t], and it is the same term
     wherever neither [t] nor any substituted lambda body has a binder.

     [subst] reduces [(\x1 .. \xn. b) a1 .. an] one argument at a time, and
     each step renames every binder still ahead of it with a traversal of
     [b], so one full application costs about n^2/2 traversals of [b].  Here
     an application of a lambda whose body mentions none of its parameters,
     to exactly as many arguments as it has parameters, is replaced by that
     body in one step, which is what the reduction would arrive at.  Every
     other occurrence -- of a lambda whose body reads a parameter, or a
     partial application of any -- is left to [subst], as are the binders of
     [t] when such occurrences remain.  The variables of [env] must not be
     rebound inside [t] (fresh names, as template holes are). *)
  let subst_up_to_bound_names env term =
    let closed, rest =
      Map.Poly.partition_map env ~f:(fun lam ->
          let params, body = let_lam lam in
          if
            Set.for_all (fvs_of body) ~f:(fun x ->
                not (List.Assoc.mem params ~equal:Ident.tvar_equal x))
          then First (List.length params, body)
          else Second lam)
    in
    (* an occurrence of a closed entry that [go] could not replace, a partial
       application; [subst] below then takes the whole of [env] *)
    let leftover = ref false in
    let term =
      if Map.Poly.is_empty closed then term
      else
        let rec go t =
          match t with
          | App (t1, t2, info) -> (
              match let_apps t with
              | Var (x, _), args -> (
                  match Map.Poly.find closed x with
                  | Some (n, body) when n = List.length args -> body
                  | _ -> App (go t1, go t2, info))
              | _ -> App (go t1, go t2, info))
          | Var (x, _) -> (
              match Map.Poly.find closed x with
              | Some (0, body) -> body
              | Some _ ->
                  leftover := true;
                  t
              | None -> t)
          | Con _ -> t
          | Bin (b, v, srt, body, info) -> Bin (b, v, srt, go body, info)
          | Let (v, srt, t1, t2, info) -> Let (v, srt, go t1, go t2, info)
          | TyApp (t1, srt, info) -> TyApp (go t1, srt, info)
          | TyLam (sv, t1, info) -> TyLam (sv, go t1, info)
        in
        go term
    in
    if !leftover then subst env term
    else if Map.Poly.is_empty rest then term
    else subst rest term

  (* [subst env t] up to the names of bound variables, in time linear in the
     size of what is built.

     Contract: where [t] and every term in [env]'s range are beta-normal, the
     result is alpha-equivalent to [subst env t]: every variable of [env] free
     in [t] is replaced, capture-avoidingly, and every redex the replacement
     creates -- a lambda of [env] applied to arguments, and whatever redex
     that reduction creates in turn -- is reduced.  A redex already present
     in [t] or in [env]'s range is not guaranteed to be reduced.

     [subst] renames every binder it passes, with a traversal of the binder's
     body, and reduces [(\x1 .. \xn. b) a1 .. an] one argument at a time, each
     step a further such traversal of [b]; a lambda whose body nests binders d
     deep therefore costs about n times d traversals of its body per
     application.  A solution recovered by predicate elimination can be a
     body of 190,000 nodes with binders nested 467 deep, and substituting it
     into one constraint took a minute.  Here all of an application's
     arguments are substituted into the body in one traversal, and a binder
     is renamed only when its name is free in a term that may be substituted
     under it, which is the only case where keeping it could capture. *)
  let subst_rename_on_capture env =
    let fvs_of_terms ts =
      List.fold ts ~init:Set.Poly.empty ~f:(fun acc t ->
          Set.union acc (fvs_of t))
    in
    (* [avoid] holds every variable free in [env]'s range *)
    let rec go env avoid t =
      if Map.Poly.is_empty env then t
      else
        match t with
        | Var (x, _) -> (
            match Map.Poly.find env x with Some u -> u | None -> t)
        | Con _ -> t
        | App _ ->
            let head, args = let_apps t in
            apply (go env avoid head) (List.map args ~f:(go env avoid))
        | Bin (b, v, srt, body, info) ->
            let env = Map.Poly.remove env v in
            if Set.mem avoid v then
              let v' = Ident.mk_fresh_tvar () in
              Bin
                ( b,
                  v',
                  srt,
                  go (Map.Poly.set env ~key:v ~data:(mk_var v')) avoid body,
                  info )
            else Bin (b, v, srt, go env avoid body, info)
        | Let (v, srt, t1, t2, info) ->
            let t1 = go env avoid t1 in
            let env2 = Map.Poly.remove env v in
            if Set.mem avoid v then
              let v' = Ident.mk_fresh_tvar () in
              Let
                ( v',
                  srt,
                  t1,
                  go (Map.Poly.set env2 ~key:v ~data:(mk_var v')) avoid t2,
                  info )
            else Let (v, srt, t1, go env2 avoid t2, info)
        | TyApp (t1, srt, info) -> TyApp (go env avoid t1, srt, info)
        | TyLam (sv, t1, info) -> TyLam (sv, go env avoid t1, info)
    (* [head args] with [head] and [args] already substituted, reducing a
       lambda head by all the arguments it takes at once *)
    and apply head args =
      match (head, args) with
      | Bin (Lambda, _, _, _, _), _ :: _ ->
          let params, body = let_lam head in
          let k = Int.min (List.length params) (List.length args) in
          let now_params, later_params = List.split_n params k in
          let now, later = List.split_n args k in
          (* a later parameter of the same name shadows an earlier one, so
             the binding made last wins, as reducing one at a time gives *)
          let env =
            List.fold2_exn now_params now ~init:Map.Poly.empty
              ~f:(fun env (x, _) a -> Map.Poly.set env ~key:x ~data:a)
          in
          apply
            (go env (fvs_of_terms now) (mk_lambda later_params body))
            later
      | _ -> mk_apps head args
    in
    let avoid =
      Map.Poly.fold env ~init:Set.Poly.empty ~f:(fun ~key:_ ~data acc ->
          Set.union acc (fvs_of data))
    in
    fun term -> go env avoid term

  (* [subst_up_to_bound_names] with every substitution it would hand to
     [subst] -- the entries whose body reads their parameters, and the whole
     map where a closed entry is partially applied -- done by
     [subst_rename_on_capture] instead.  Same contract: where [term] and
     [env]'s range are beta-normal, the result is alpha-equivalent to
     [subst env term]; in time linear in what is built, and it draws a fresh
     name only for a binder that could capture. *)
  let subst_up_to_bound_names_linear env term =
    let closed, rest =
      Map.Poly.partition_map env ~f:(fun lam ->
          let params, body = let_lam lam in
          if
            Set.for_all (fvs_of body) ~f:(fun x ->
                not (List.Assoc.mem params ~equal:Ident.tvar_equal x))
          then First (List.length params, body)
          else Second lam)
    in
    let leftover = ref false in
    let term' =
      if Map.Poly.is_empty closed then term
      else
        let rec go t =
          match t with
          | App (t1, t2, info) -> (
              match let_apps t with
              | Var (x, _), args -> (
                  match Map.Poly.find closed x with
                  | Some (n, body) when n = List.length args -> body
                  | _ -> App (go t1, go t2, info))
              | _ -> App (go t1, go t2, info))
          | Var (x, _) -> (
              match Map.Poly.find closed x with
              | Some (0, body) -> body
              | Some _ ->
                  leftover := true;
                  t
              | None -> t)
          | Con _ -> t
          | Bin (b, v, srt, body, info) -> Bin (b, v, srt, go body, info)
          | Let (v, srt, t1, t2, info) -> Let (v, srt, go t1, go t2, info)
          | TyApp (t1, srt, info) -> TyApp (go t1, srt, info)
          | TyLam (sv, t1, info) -> TyLam (sv, go t1, info)
        in
        go term
    in
    if !leftover then subst_rename_on_capture env term
    else if Map.Poly.is_empty rest then term'
    else subst_rename_on_capture rest term'

  let refresh (senv, t) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ()) in
    (Map.rename_keys_map map senv, rename map t)

  let rec unify t1 t2 =
    match (t1, t2) with
    | Var (tvar, _), t | t, Var (tvar, _) ->
        (* ToDo: occurs check *)
        Map.Poly.singleton tvar t |> Option.some
    | App (Var (tvar1, _), t1, _), App (Var (tvar2, _), t2, _) ->
        if Stdlib.(tvar1 = tvar2) then unify t1 t2 else None
    | Con (s1, _), Con (s2, _) ->
        if Stdlib.(s1 = s2) then Some Map.Poly.empty else None
    | App (t11, t12, _), App (t21, t22, _) -> (
        match (unify t11 t21, unify t12 t22) with
        | Some th1, Some th2 ->
            Map.fold th1 ~init:th2 ~f:(fun ~key ~data map ->
                match Map.Poly.add ~key ~data map with
                | `Ok map' -> map'
                | _ -> map)
            |> Option.some
        | _, _ -> None)
    | _ -> None

  (** Evaluation *)

  let open_assert_sort_check assert_sort_check_of sort = function
    | FunLit _ -> (
        match sort with Sort.SArrow (_, _) -> () | _ -> assert false)
    | SFunLit _ -> assert false
    | lit -> assert_sort_check_of sort lit

  let rec open_eval eval_sym of_termlit type_env = function
    | Var _ -> failwith "Term variables should be removed before evaluation "
    | Con (sym, _) -> eval_sym sym
    | App (Bin (Lambda, v, _sort, term, _), t2, _) ->
        open_eval eval_sym of_termlit type_env
        @@ subst (Map.Poly.singleton v t2) term
    | App (t1, t2, _) -> (
        match open_eval eval_sym of_termlit type_env t1 with
        | FunLit flit -> flit (open_eval eval_sym of_termlit type_env t2)
        | _ -> failwith "the term cannot be applyed")
    | Let (x, _, t1, t2, _) ->
        let l1 = open_eval eval_sym of_termlit type_env t1 in
        open_eval eval_sym of_termlit type_env
        @@ subst (Map.Poly.singleton x @@ of_termlit l1) t2
    | Bin (_, _, _, _, _) -> failwith "eval of Lam is not implemented yet"
    | TyApp (term, sort, _) -> (
        match open_eval eval_sym of_termlit type_env term with
        | SFunLit sfun -> sfun sort
        | _ -> failwith "invalid type for TyApp")
    | TyLam (_, _, _) -> failwith "invalid type for TyLam"

  let is_termlit _ = false
  let of_termlit _ = failwith "Term.of_termlit"
  let assert_sort_check _ _ = failwith "Term.assert_sort_check"
  let eval_sym _ = failwith "Term.eval_sym"
  let eval _ _ = failwith "Term.eval"

  (* assume that term is let-normalized and alpha-renamed *)

  (** Observation *)

  let rec let_sort_env_of = function
    | Let (v, s, _, b, _) ->
        Map.Poly.add_exn ~key:v ~data:s @@ let_sort_env_of b
    | _ -> Map.Poly.empty

  (* assume that term is let-normalized and alpha-renamed *)
  let rec let_env_of ?(map = Map.Poly.empty) = function
    | Let (var, _, def, body, _) ->
        let_env_of ~map:(Map.Poly.set map ~key:var ~data:(subst map def)) body
    | _ -> Map.Poly.empty

  (** Transformation *)

  let reduce_sort_map (senv, t) =
    (Map.Poly.filter_keys senv ~f:(Set.mem @@ fvs_of t), t)
end

module type BoolTermType = sig
  include TermType

  type sym +=
    | True
    | False
    | Not
    | And
    | Or
    | Imply
    | Iff
    | Xor
    | IfThenElse
    | Eq
    | Neq

  type Sort.t += SBool
  type termlit += BoolLit of bool

  (** Construction *)

  val mk_bool : bool -> term
  val mk_and : unit -> term
  val mk_or : unit -> term
  val mk_not : unit -> term
  val mk_imply : unit -> term
  val mk_xor : unit -> term
  val mk_iff : unit -> term
  val mk_ite : Sort.t -> term
  val mk_bool_ite : unit -> term
  val mk_eq : Sort.t -> term
  val mk_neq : Sort.t -> term
  val mk_bool_eq : unit -> term
  val mk_bool_neq : unit -> term
  val and_of : term list -> term
  val or_of : term list -> term
  val or_of_parts : (term * term) list -> term

  val fold_or_of_parts :
    bool:(bool -> 'a) -> or_:('a -> 'a -> 'a) -> (term * 'a) list -> 'a
  val neg_of : term -> term
  val imply_of : term -> term -> term
  val eq_of : Sort.t -> term -> term -> term
  val neq_of : Sort.t -> term -> term -> term
  val ite_of : Sort.t -> term -> term -> term -> term
  val mk_forall : sort_env_list -> term -> term
  val mk_exists : sort_env_list -> term -> term
  val forall : sort_env_list -> term -> term
  val exists : sort_env_list -> term -> term

  (** Destruction *)

  val let_not : term -> term

  (** Observation *)

  val is_bool : term -> bool
  val is_bool_sort : Sort.t -> bool
  val is_true : term -> bool
  val is_false : term -> bool
  val is_not : term -> bool
  val is_pvar_app : sort_env_map -> sort_env_map -> term -> bool
  val conjuncts_of : term -> term list
  val disjuncts_of : term -> term list

  (** Transformation *)

  val cnf_of :
    sort_env_map ->
    sort_env_map ->
    term ->
    (term Set.Poly.t * term Set.Poly.t * term) Set.Poly.t

  val cnf_of_guarded :
    sort_env_map ->
    sort_env_map ->
    term ->
    (term Set.Poly.t * term Set.Poly.t * term) Set.Poly.t

  val nnf_of : term -> term
  val elim_imp : term -> term

  val with_shared_nnf_cnf : (unit -> 'a) -> 'a
  (** [with_shared_nnf_cnf f] runs [f] with tables, local to this domain and
      dropped when [f] returns or raises, in which [nnf_of] remembers the
      image of every node it meets and [cnf_of] whether a subterm mentions an
      unknown, both by physical identity: the same results as outside, the
      images shared wherever their arguments were *)
end

module BoolTerm : BoolTermType = struct
  include Term

  type sym +=
    | True
    | False
    | Not
    | And
    | Or
    | Imply
    | Iff
    | Xor
    | IfThenElse
    | Eq
    | Neq

  type Sort.t += SBool
  type termlit += BoolLit of bool

  (** Sorts *)

  let bb = Sort.mk_arrow SBool SBool
  let bbb = Sort.mk_arrow SBool bb

  let sym_sort_map =
    Map.Poly.of_alist_exn
      [
        (True, SBool);
        (False, SBool);
        (Not, bb);
        (And, bbb);
        (Or, bbb);
        (Imply, bbb);
        (Iff, bbb);
        (Xor, bbb);
        ( IfThenElse,
          let var = Ident.mk_fresh_svar () in
          Sort.SForAll
            ( var,
              Sort.mk_arrow SBool
              @@ Sort.mk_arrow (Sort.SVar var)
              @@ Sort.mk_arrow (Sort.SVar var)
              @@ Sort.SVar var ) );
        ( Eq,
          let var = Ident.mk_fresh_svar () in
          Sort.SForAll
            ( var,
              Sort.mk_arrow (Sort.SVar var)
              @@ Sort.mk_arrow (Sort.SVar var) SBool ) );
        ( Neq,
          let var = Ident.mk_fresh_svar () in
          Sort.SForAll
            ( var,
              Sort.mk_arrow (Sort.SVar var)
              @@ Sort.mk_arrow (Sort.SVar var) SBool ) );
      ]

  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)

  let str_of_sym = function
    | True -> "True"
    | False -> "False"
    | Not -> "Not"
    | And -> "And"
    | Or -> "Or"
    | Imply -> "Imply"
    | Iff -> "Iff"
    | Xor -> "Xor"
    | IfThenElse -> "IfThenElse"
    | Eq -> "Eq"
    | Neq -> "Neq"
    | _ -> failwith "BoolTerm.str_of_sym"

  let str_of_termlit = function
    | BoolLit true -> "true"
    | BoolLit false -> "false"
    | _ -> assert false

  let str_of_sort_theory = function
    | SBool -> "bool"
    | _ -> failwith "unknown sort in BoolTerm.str_of_sort_theory"

  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Construction *)

  let mk_bool b = if b then mk_con True else mk_con False
  let mk_and () = mk_con And
  let mk_or () = mk_con Or
  let mk_not () = mk_con Not
  let mk_imply () = mk_con Imply
  let mk_xor () = mk_con Xor
  let mk_iff () = mk_con Iff
  let mk_ite = mk_tyapp (mk_con IfThenElse)
  let mk_bool_ite () = mk_ite SBool
  let mk_eq = mk_tyapp (mk_con Eq)
  let mk_neq = mk_tyapp (mk_con Neq)
  let mk_bool_eq () = mk_eq SBool
  let mk_bool_neq () = mk_neq SBool

  let and_of phis =
    let rec aux acc = function
      | [] -> ( match acc with None -> mk_bool true | Some phi -> phi)
      | Con (True, _) :: phis' -> aux acc phis'
      | Con (False, _) :: _ -> mk_bool false
      | phi :: phis' -> (
          match acc with
          | None -> aux (Some phi) phis'
          | Some phi' -> aux (Some (mk_apps (mk_and ()) [ phi'; phi ])) phis')
    in
    aux None phis

  let or_of phis =
    let rec aux acc = function
      | [] -> ( match acc with None -> mk_bool false | Some phi -> phi)
      | Con (False, _) :: phis' -> aux acc phis'
      | Con (True, _) :: _ -> mk_bool true
      | phi :: phis' -> (
          match acc with
          | None -> aux (Some phi) phis'
          | Some phi' -> aux (Some (mk_apps (mk_or ()) [ phi'; phi ])) phis')
    in
    aux None phis

  (* [or_of_parts parts], for [parts] a list of pairs [(phi, phi')]: the
     disjunction [or_of] builds from the [phi]s -- the same constants dropped,
     the same stop at a [true], the same left-nested shape -- with each [phi]
     replaced by its [phi'].

     Contract: for a map [f] that sends every constant to itself and
     distributes over an application of [Or] to two arguments,
     [or_of_parts (List.map phis ~f:(fun p -> (p, f p)))] is [f (or_of phis)].
     A caller substituting into many disjunctions that share most of their
     disjuncts substitutes the shared ones once and assembles each
     disjunction with this. *)
  let or_of_parts parts =
    let rec aux acc = function
      | [] -> ( match acc with None -> mk_bool false | Some phi -> phi)
      | (Con (False, _), _) :: parts' -> aux acc parts'
      | (Con (True, _), _) :: _ -> mk_bool true
      | (_, phi) :: parts' -> (
          match acc with
          | None -> aux (Some phi) parts'
          | Some phi' -> aux (Some (mk_apps (mk_or ()) [ phi'; phi ])) parts')
    in
    aux None parts

  (* [or_of_parts] with the result built in another representation: [bool b]
     stands for the constant [b] and [or_ a b] for the disjunction of two
     parts already built.  The constants are recognised on each pair's first
     component, as [or_of_parts] recognises them.

     Contract: for a map [g] with [g (mk_bool b) = bool b] and
     [g (Or t1 t2) = or_ (g t1) (g t2)],
     [fold_or_of_parts ~bool ~or_ (List.map parts ~f:(fun (p, p') -> (p, g p')))]
     is [g (or_of_parts parts)]. *)
  let fold_or_of_parts ~bool ~or_ parts =
    let rec aux acc = function
      | [] -> ( match acc with None -> bool false | Some phi -> phi)
      | (Con (False, _), _) :: parts' -> aux acc parts'
      | (Con (True, _), _) :: _ -> bool true
      | (_, phi) :: parts' -> (
          match acc with
          | None -> aux (Some phi) parts'
          | Some phi' -> aux (Some (or_ phi' phi)) parts')
    in
    aux None parts

  let rec neg_of = function
    | Let (v, s, d, b, i) -> Let (v, s, d, neg_of b, i)
    | term -> mk_app (mk_not ()) term

  let imply_of t1 t2 = mk_apps (mk_imply ()) [ t1; t2 ]
  let eq_of ty t1 t2 = mk_apps (mk_eq ty) [ t1; t2 ]
  let neq_of ty t1 t2 = mk_apps (mk_neq ty) [ t1; t2 ]
  let ite_of ty t1 t2 t3 = mk_apps (mk_ite ty) [ t1; t2; t3 ]

  let mk_forall args term =
    List.fold_right args ~init:term ~f:(Tuple2.uncurry (mk_bind Forall))

  let mk_exists args term =
    List.fold_right args ~init:term ~f:(Tuple2.uncurry (mk_bind Exists))

  let forall = mk_binds Forall
  let exists = mk_binds Exists

  (** Destruction *)

  let let_not t =
    match let_app t with Con (Not, _), t, _ -> t | _, _, _ -> assert false

  (** Evaluation *)

  let is_termlit = function BoolLit _ -> true | _ -> false
  let of_termlit = function BoolLit b -> mk_bool b | _ -> assert false

  let assert_sort_check_of_theory sort lit =
    match (sort, lit) with SBool, BoolLit _ -> () | _ -> assert false

  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory

  let eval_sym = function
    | True -> BoolLit true
    | False -> BoolLit false
    | Not ->
        FunLit (function BoolLit x -> BoolLit (not x) | _ -> assert false)
    | And ->
        FunLit
          (function
          | BoolLit x ->
              FunLit
                (function BoolLit y -> BoolLit (x && y) | _ -> assert false)
          | _ -> assert false)
    | Or ->
        FunLit
          (function
          | BoolLit x ->
              FunLit
                (function BoolLit y -> BoolLit (x || y) | _ -> assert false)
          | _ -> assert false)
    | Imply ->
        FunLit
          (function
          | BoolLit x ->
              FunLit
                (function
                | BoolLit y -> BoolLit ((not x) || y)
                | _ -> assert false)
          | _ -> assert false)
    | Iff ->
        FunLit
          (function
          | BoolLit x ->
              FunLit
                (function
                | BoolLit y -> BoolLit Stdlib.(x = y)
                | _ -> assert false)
          | _ -> assert false)
    | Xor ->
        FunLit
          (function
          | BoolLit x ->
              FunLit
                (function
                | BoolLit y -> BoolLit Stdlib.(x <> y)
                | _ -> assert false)
          | _ -> assert false)
    | IfThenElse ->
        SFunLit
          (fun sort ->
            FunLit
              (function
              | BoolLit t1 ->
                  FunLit
                    (fun l2 ->
                      assert_sort_check sort l2;
                      FunLit
                        (fun l3 ->
                          assert_sort_check sort l3;
                          if t1 then l2 else l3))
              | _ -> assert false))
    | Eq ->
        SFunLit
          (fun sort ->
            FunLit
              (fun l1 ->
                assert_sort_check sort l1;
                FunLit
                  (fun l2 ->
                    assert_sort_check sort l2;
                    BoolLit Stdlib.(l1 = l2))))
    | Neq ->
        SFunLit
          (fun sort ->
            FunLit
              (fun l1 ->
                assert_sort_check sort l1;
                FunLit
                  (fun l2 ->
                    assert_sort_check sort l2;
                    BoolLit Stdlib.(l1 <> l2))))
    | _ -> assert false

  let eval = open_eval eval_sym of_termlit

  (** Observation *)

  let is_bool term =
    if is_con term then
      let sym, _ = let_con term in
      Stdlib.(sym = True) || Stdlib.(sym = False)
    else false

  let is_bool_sort = function SBool -> true | _ -> false

  let is_true term =
    if is_con term then
      let sym, _ = let_con term in
      Stdlib.(sym = True)
    else false

  let is_false term =
    if is_con term then
      let sym, _ = let_con term in
      Stdlib.(sym = False)
    else false

  let is_not term =
    if is_app term then
      let t, _, _ = let_app term in
      if is_con t then
        let sym, _ = let_con t in
        Stdlib.(sym = Not)
      else false
    else false

  let rec is_pvar_app exi_senv uni_senv = function
    | Var (tvar, _) -> (
        match (Map.Poly.find exi_senv tvar, Map.Poly.find uni_senv tvar) with
        | Some sort, None -> is_bool_sort @@ Sort.ret_of sort
        | None, Some _ -> false
        | Some _, Some _ ->
            failwith
              (sprintf "[is_pvar_app] %s is bound twice"
                 (Ident.name_of_tvar tvar))
        | None, None ->
            failwith
              (sprintf "[is_pvar_app] %s is not bound" (Ident.name_of_tvar tvar))
        )
    | App (t, _, _) -> is_pvar_app exi_senv uni_senv t
    | _ -> false

  let rec is_fvar_app fenv = function
    | Var (tvar, _) -> Map.Poly.mem fenv tvar
    | App (t, _, _) -> is_fvar_app fenv t
    | _ -> false

  (* The operands of a nest of applications of a symbol [is_op] accepts, left
     to right.  The list is built onto an accumulator: [and_of] and [or_of]
     nest to the left, and appending the left operand's list at every level,
     as a [concat_map] does, made this quadratic in the number of operands,
     which on a resolvent of tens of thousands of disjuncts was most of the
     time of the passes that start by listing them. *)
  let operands_of is_op t =
    let rec go t acc =
      match t with
      | App (_, _, _) -> (
          match let_apps t with
          | Con (op, _), args when is_op op ->
              List.fold_right args ~init:acc ~f:go
          | _, _ -> t :: acc)
      | t -> t :: acc
    in
    go t []

  let conjuncts_of = operands_of (function And -> true | _ -> false)
  let disjuncts_of = operands_of (function Or -> true | _ -> false)

  (** Transformation *)

  let insert_let var sort def info term =
    if Set.mem (fvs_of term) var then
      let var' = Ident.mk_fresh_tvar () in
      Let (var', sort, def, rename (Map.Poly.singleton var var') term, info)
    else term

  let insert_let_var_app var sort def info atom =
    let x, ts = let_var_app atom in
    mk_var_app x @@ List.map ts ~f:(insert_let var sort def info)

  (* Physical tables for [nnf_of] and for the unknown test of [cnf_of]: on a
     set of clauses whose pure parts are disjunctions of the same physical
     subformulas, both walked every shared subformula once per clause, and
     [nnf_of] rebuilt it once per clause, so a set that shares its parts
     came out of one pass with every part copied.  Keys are compared by
     physical identity, and hashed by address
     ([Common.Ext.Hashtbl.phys_hash]), which only spreads the buckets.  The unknown test is remembered with the set of unknowns it
     was asked for, and reused for an equal set. *)
  module NnfPhysTbl = Stdlib.Hashtbl.Make (struct
    type t = term

    let equal = phys_equal
    let hash = Common.Ext.Hashtbl.phys_hash
  end)

  type nnf_cnf_tables = {
    nnf_tbl : term NnfPhysTbl.t;
    none_tbl : (Ident.tvar Set.Poly.t * bool) NnfPhysTbl.t;
  }

  let nnf_cnf_scope : nnf_cnf_tables option Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  let with_shared_nnf_cnf f =
    match Domain.DLS.get nnf_cnf_scope with
    | Some _ -> f ()
    | None ->
        Domain.DLS.set nnf_cnf_scope
          (Some
             {
               nnf_tbl = NnfPhysTbl.create 1024;
               none_tbl = NnfPhysTbl.create 1024;
             });
        Exn.protect ~f ~finally:(fun () -> Domain.DLS.set nnf_cnf_scope None)

  let rec nnf_of t =
    match Domain.DLS.get nnf_cnf_scope with
    | None -> nnf_of_node t
    | Some tbls -> (
        match NnfPhysTbl.find_opt tbls.nnf_tbl t with
        | Some t' -> t'
        | None ->
            let t' = nnf_of_node t in
            NnfPhysTbl.add tbls.nnf_tbl t t';
            t')

  and nnf_of_node = function
    | App (Con (Not, _), Con (True, _), _) ->
        (* not true -> false *)
        mk_bool false
    | App (Con (Not, _), Con (False, _), _) ->
        (* not false -> true *)
        mk_bool true
    | App (Con (Not, _), App (Con (Not, _), t, _), _) ->
        (* not (not t) -> t *)
        nnf_of t
    | App (Con (Not, _), App (App (Con (And, _), t1, _), t2, _), _) ->
        (* not (t1 and t2) -> (not t1) or (not t2) *)
        mk_apps (mk_or ()) [ nnf_of @@ neg_of t1; nnf_of @@ neg_of t2 ]
    | App (Con (Not, _), App (App (Con (Or, _), t1, _), t2, _), _) ->
        (* not (t1 or t2) -> (not t1) and (not t2) *)
        mk_apps (mk_and ()) [ nnf_of @@ neg_of t1; nnf_of @@ neg_of t2 ]
    | App (Con (Not, _), App (App (Con (Imply, _), t1, _), t2, _), _) ->
        (* not (t1 => t2) -> t1 and (not t2) *)
        mk_apps (mk_and ()) [ nnf_of t1; nnf_of @@ neg_of t2 ]
    | App (Con (Not, _), App (App (Con (Iff, _), t1, _), t2, _), _) ->
        (* not (t1 <=> t2) -> t1 <> t2 *)
        mk_apps (mk_neq SBool) [ nnf_of t1; nnf_of t2 ]
    | App (Con (Not, _), App (App (Con (Xor, _), t1, _), t2, _), _) ->
        (* not (t1 xor t2) -> t1 = t2 *)
        mk_apps (mk_eq SBool) [ nnf_of t1; nnf_of t2 ]
    | App (Con (Not, _), Bin (Forall, x, s, t, _), _) ->
        mk_bind Exists x s (nnf_of @@ neg_of t)
    | App (Con (Not, _), Bin (Exists, x, s, t, _), _) ->
        mk_bind Forall x s (nnf_of @@ neg_of t)
    | App (Con (Not, _), Let (v, s, d, b, _), _) ->
        mk_let v s (nnf_of d) (nnf_of @@ neg_of b)
    | App (Con (Not, _), t, _) as term -> (
        match let_apps t with
        | TyApp (Con (Eq, _), s, _), [ t1; t2 ] ->
            nnf_of @@ mk_apps (mk_neq s) [ t1; t2 ]
        | TyApp (Con (Neq, _), s, _), [ t1; t2 ] ->
            nnf_of @@ mk_apps (mk_eq s) [ t1; t2 ]
        | _ -> term)
    | App (App (Con (And, _), t1, _), t2, _) ->
        mk_apps (mk_and ()) [ nnf_of t1; nnf_of t2 ]
    | App (App (Con (Or, _), t1, _), t2, _) ->
        mk_apps (mk_or ()) [ nnf_of t1; nnf_of t2 ]
    | App (App (Con (Imply, _), t1, _), t2, _) ->
        mk_apps (mk_or ()) [ nnf_of @@ neg_of t1; nnf_of t2 ]
    | App (App (Con (Iff, _), t1, _), t2, _) ->
        (* t1 <=> t2 -> t1 = t2 *)
        nnf_of @@ mk_apps (mk_eq SBool) [ t1; t2 ]
    | App (App (Con (Xor, _), t1, _), t2, _) ->
        (* t1 xor t2 -> t1 <> t2 *)
        nnf_of @@ mk_apps (mk_neq SBool) [ t1; t2 ]
    | Bin (b, x, s, t, _) -> mk_bind b x s (nnf_of t)
    | Let (v, s, d, b, _) -> mk_let v s (nnf_of d) (nnf_of b)
    | term -> (
        match let_apps term with
        | TyApp (Con (Eq, _), SBool, _), [ t1; t2 ] ->
            mk_apps (mk_eq SBool) [ nnf_of t1; nnf_of t2 ]
        (* t1 = t2 -> (t1 and t2) or (not t1 and not t2) *)
        (*mk_apps (mk_or ()) [mk_apps (mk_and ()) [nnf_of t1; nnf_of t2];
                             mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]]*)
        (* t1 = t2 -> (not t1 or t2) and (t1 or not t2) *)
        (*mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of t2];
                             mk_apps (mk_or ()) [nnf_of t1; nnf_of @@ neg_of t2]]*)
        | TyApp (Con (Neq, _), SBool, _), [ t1; t2 ] ->
            mk_apps (mk_neq SBool) [ nnf_of t1; nnf_of t2 ]
        (* t1 <> t2 -> (t1 and not t2) or (not t1 and t2) *)
        (*mk_apps (mk_or ()) [mk_apps (mk_and ()) [nnf_of t1; nnf_of @@ neg_of t2];
                             mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of t2]]*)
        (* t1 <> t2 -> (t1 or t2) and (not t1 or not t2) *)
        (*mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of t1; nnf_of t2];
                             mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]]*)
        | _ -> term)

  (* Does [t] mention one of [unknowns] freely?  [fvs_of] answers that by
     building the whole free-variable set of [t] and handing it to a
     disjointness test against the key set of the signature, rebuilt from the
     map at every call -- two full walks and two sets thrown away at every node
     of the recursion below, where on the great majority of nodes the subterm
     mentions no unknown at all.  Asked directly, the question stops at the
     first unknown met and allocates nothing on the way.  The exclusions are
     [fvs_of]'s: a variable bound inside [t] (a [Let] binds its variable in the
     definition as well as in the body there), a dummy variable, and a name of
     the process-global function environment; the cheap membership test comes
     first so that the two lookups are paid only for a variable that is an
     unknown. *)
  let rec mentions_none_of unknowns bound = function
    | Var (var, _) ->
        (not (Set.mem unknowns var))
        || Set.mem bound var
        || LogicOld.is_dummy_term var None
        || Map.Poly.mem (LogicOld.get_fenv ()) var
    | Con (_, _) -> true
    | App (t1, t2, _) ->
        mentions_none_of unknowns bound t1 && mentions_none_of unknowns bound t2
    | Bin (_, var, _, t1, _) -> mentions_none_of unknowns (Set.add bound var) t1
    | Let (var, _, t1, t2, _) ->
        let bound = Set.add bound var in
        mentions_none_of unknowns bound t1 && mentions_none_of unknowns bound t2
    | TyApp (t, _, _) | TyLam (_, t, _) -> mentions_none_of unknowns bound t

  (* [mentions_none_of unknowns Set.Poly.empty t], remembered in a scope of
     [with_shared_nnf_cnf] at application nodes, whose answer is the
     conjunction of their two sides' (an application binds nothing); a
     binder is asked as before *)
  let rec mentions_none_of_closed unknowns t =
    match (t, Domain.DLS.get nnf_cnf_scope) with
    | App (t1, t2, _), Some tbls -> (
        match NnfPhysTbl.find_opt tbls.none_tbl t with
        | Some (us, b) when phys_equal us unknowns || Set.equal us unknowns ->
            b
        | _ ->
            let b =
              mentions_none_of_closed unknowns t1
              && mentions_none_of_closed unknowns t2
            in
            NnfPhysTbl.replace tbls.none_tbl t (unknowns, b);
            b)
    | _ -> mentions_none_of unknowns Set.Poly.empty t

  let rec aux ~guarded exi_senv unknowns senv t k =
    match t with
    | Con (True, _) | App (Con (Not, _), Con (False, _), _) -> k Set.Poly.empty
    | Con (False, _) | App (Con (Not, _), Con (True, _), _) ->
        k @@ Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | t when mentions_none_of_closed unknowns t ->
        k
        @@ Set.Poly.singleton
             (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton t)
    | App (Con (Not, _), t, _) ->
        if is_pvar_app exi_senv senv t then
          k
          @@ Set.Poly.singleton
               (Set.Poly.empty, Set.Poly.singleton t, Set.Poly.empty)
        else
          (* not reachable? *)
          k
          @@ Set.Poly.singleton
               (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (neg_of t))
    | App (App (Con (And, _), t1, _), t2, _) ->
        aux ~guarded exi_senv unknowns senv t1 (fun res1 ->
            aux ~guarded exi_senv unknowns senv t2 (fun res2 ->
                let phis, cls =
                  Set.union res1 res2
                  |> Set.partition_tf ~f:(fun (ps, ns, _) ->
                      Set.is_empty ps && Set.is_empty ns)
                  |> Tuple2.map_both
                       ~f1:(Set.Poly.map ~f:(trd3 >> Set.to_list >> or_of))
                       ~f2:Fn.id
                in
                if Set.is_empty phis then k cls
                else
                  let pure = and_of @@ Set.to_list phis in
                  let cls =
                    if guarded && not (Set.is_empty cls) then
                      let guard = nnf_of @@ neg_of pure in
                      Set.Poly.map cls ~f:(fun (ps, ns, phis') ->
                          (ps, ns, Set.add phis' guard))
                    else cls
                  in
                  k
                  @@ Set.add cls
                       (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton pure)))
    | App (App (Con (Or, _), t1, _), t2, _) ->
        aux ~guarded exi_senv unknowns senv t1 (fun res1 ->
            aux ~guarded exi_senv unknowns senv t2 (fun res2 ->
                k
                @@ Set.cartesian_map res1 res2
                     ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
                       ( Set.union ps1 ps2,
                         Set.union ns1 ns2,
                         Set.union phis1 phis2 ))))
    | Let (var, sort, def, body, info) ->
        aux ~guarded exi_senv unknowns (Map.Poly.set senv ~key:var ~data:sort) body
          (fun res ->
            k
            @@ Set.Poly.map res ~f:(fun (ps, ns, phis) ->
                ( Set.Poly.map ~f:(insert_let_var_app var sort def info) ps,
                  Set.Poly.map ~f:(insert_let_var_app var sort def info) ns,
                  Set.Poly.singleton
                  @@ insert_let var sort def info
                  @@ or_of @@ Set.to_list phis )))
    | t -> (
        if is_pvar_app exi_senv senv t then
          k
          @@ Set.Poly.singleton
               (Set.Poly.singleton t, Set.Poly.empty, Set.Poly.empty)
        else if mentions_none_of_closed unknowns t then
          k
          @@ Set.Poly.singleton
               (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton t)
        else
          let fenv = LogicOld.get_fenv () in
          match let_apps t with
          | TyApp (Con (Eq, _), SBool, _), [ t1; t2 ]
            when (not (is_fvar_app fenv t1)) && not (is_fvar_app fenv t2) ->
              (* t1 = t2 -> (not t1 or t2) and (t1 or not t2) *)
              aux ~guarded exi_senv unknowns senv
                (mk_apps (mk_and ())
                   [
                     mk_apps (mk_or ()) [ nnf_of @@ neg_of t1; nnf_of t2 ];
                     mk_apps (mk_or ()) [ nnf_of t1; nnf_of @@ neg_of t2 ];
                   ])
                k
          | TyApp (Con (Neq, _), SBool, _), [ t1; t2 ]
            when (not (is_fvar_app fenv t1)) && not (is_fvar_app fenv t2) ->
              (* t1 <> t2 -> (t1 or t2) and (not t1 or not t2) *)
              aux ~guarded exi_senv unknowns senv
                (mk_apps (mk_and ())
                   [
                     mk_apps (mk_or ()) [ nnf_of t1; nnf_of t2 ];
                     mk_apps (mk_or ())
                       [ nnf_of @@ neg_of t1; nnf_of @@ neg_of t2 ];
                   ])
                k
          | _ ->
              (* not reachable *)
              k
              @@ Set.Poly.singleton
                   (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton t))

  let cnf_with ~guarded exi_senv uni_senv t =
    Set.Poly.map ~f:(fun (pos, neg, phis) ->
        (pos, neg, or_of @@ Set.to_list phis))
    @@ aux ~guarded exi_senv (Map.key_set exi_senv) uni_senv t Fn.id

  (* assume that [term] is in NNF *)
  let cnf_of exi_senv uni_senv t = cnf_with ~guarded:false exi_senv uni_senv t

  (* [cnf_of] with every clause that comes from a conjunct mentioning an
     unknown guarded by the negation of the conjunction's predicate-free part.
     Assumes [t] is in NNF.

     Contract: the result is a clause set equivalent to [t] (as is
     [cnf_of]'s).  At a conjunction [P /\ Y] with [P] predicate-free,
     [P /\ Y] is equivalent to [P /\ (not P \/ Y)]: where [P] holds the
     second conjunct is [Y], and where it fails both sides are false.  So a
     clause [C] of [Y] may be replaced by [not P \/ C]; under a disjunction
     [U \/ (P /\ Y)] the clauses become [U \/ P] and [U \/ not P \/ C].

     Why: a Horn engine's derivation uses one clause per step.  From the
     unguarded form [U(s) \/ (G(s) /\ not U(s'))], whose clauses are
     [U(s) \/ G(s)] and [U(s) \/ not U(s')], a derivation may step from [s]
     to [s'] where [G(s)] is false, i.e. continue a play past its end.  A
     reader that takes every derivation step as a move of the game (and asks
     a ranking to decrease along it) then asks for steps the game does not
     contain.  With the guard on the step clause, every step a derivation
     takes is one the formula allows at that state. *)
  let cnf_of_guarded exi_senv uni_senv t =
    cnf_with ~guarded:true exi_senv uni_senv t

  let rec elim_imp = function
    | App (App (Con (Imply, _), t1, _), t2, _) ->
        (* t1 => t2 -> (not t1) or t2 *)
        mk_apps (mk_or ()) [ neg_of (elim_imp t1); elim_imp t2 ]
    | App (t1, t2, _) -> mk_app (elim_imp t1) (elim_imp t2)
    | Bin (b, x, s, t, _) -> mk_bind b x s (elim_imp t)
    | Let (x, s, t1, t2, _) -> mk_let x s (elim_imp t1) (elim_imp t2)
    | TyApp (t, s, _) -> mk_tyapp (elim_imp t) s
    | TyLam (x, t, _) -> mk_tylam x (elim_imp t)
    | term -> term
end

module type IntTermType = sig
  include TermType

  type sym +=
    | Int of Z.t
    | Neg
    | Abs
    | Add
    | Sub
    | Mul
    | Div of Value.modulo
    | Rem of Value.modulo
    | Power
    | Case of int

  type Sort.t += SInt
  type termlit += IntLit of Z.t

  (** Construction *)

  val zero : unit -> term
  val one : unit -> term
  val mk_int : Z.t -> term
  val mk_from_int : int -> term
  val int_consts_of : term -> Z.t Set.Poly.t
  val mk_neg : unit -> term
  val mk_abs : unit -> term
  val mk_add : unit -> term
  val mk_sub : unit -> term
  val mk_mul : unit -> term
  val mk_div : Value.modulo -> term
  val mk_rem : Value.modulo -> term
  val mk_power : unit -> term
  val mk_case : int -> Sort.t -> term
  val sum : term list -> term
  val prod : term list -> term

  (** Observation *)

  val is_int_sort : Sort.t -> bool

  (** Evalaution *)

  val neg_sym : sym -> sym
end

module IntTerm : IntTermType = struct
  include Term

  type sym +=
    | Int of Z.t
    | Neg
    | Abs
    | Add
    | Sub
    | Mul
    | Div of Value.modulo
    | Rem of Value.modulo
    | Power
    | Case of int

  type Sort.t += SInt
  type termlit += IntLit of Z.t

  (** Sorts *)

  let ii = Sort.mk_arrow SInt SInt
  let iii = Sort.mk_arrow SInt ii

  let sym_sort_map =
    Map.Poly.of_alist_exn
      [
        (Neg, ii);
        (Abs, ii);
        (Add, iii);
        (Sub, iii);
        (Mul, iii);
        (Div Euclidean, iii);
        (Div Truncated, iii);
        (Rem Euclidean, iii);
        (Rem Truncated, iii);
        (Power, iii);
      ]

  let sort_of_sym = function
    | Int _ -> SInt
    | Case n ->
        let var = Ident.mk_fresh_svar () in
        Sort.SForAll
          ( var,
            Sort.mk_fun (SInt :: List.init (n + 1) ~f:(fun _ -> Sort.SVar var))
          )
    | sym -> Map.Poly.find_exn sym_sort_map sym

  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)

  let str_of_sym = function
    | Int n -> sprintf "Int %s" @@ Z.to_string n
    | Neg -> "Neg"
    | Abs -> "Abs"
    | Add -> "Add"
    | Sub -> "Sub"
    | Mul -> "Mul"
    | Div _ -> "Div"
    | Rem _ -> "Rem"
    | Power -> "Power"
    | Case _n -> "Case"
    | _ -> failwith "IntTerm.str_of_sym"

  let str_of_termlit = function IntLit n -> Z.to_string n | _ -> assert false

  let str_of_sort_theory = function
    | SInt -> "int"
    | _ -> failwith "unknown sort in IntTerm.str_of_sort_theory"

  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Construction *)

  let zero () = mk_con (Int Z.zero)
  let one () = mk_con (Int Z.one)
  let mk_int n = mk_con (Int n)
  let mk_from_int n = mk_con (Int (Z.of_int n))

  (* The integer literals a term mentions, by walking it.  A caller wanting
     the indices a lambda body could be sampled at wants exactly this; reading
     them out of the term's PRINTED form instead also collects any digit
     inside a sort or a generated name. *)
  let int_consts_of t =
    let rec inner acc (t : term) =
      match t with
      | Con (Int z, _) -> Set.add acc z
      | Con _ | Var _ -> acc
      | App (t1, t2, _) -> inner (inner acc t1) t2
      | Bin (_, _, _, t1, _) -> inner acc t1
      | Let (_, _, t1, t2, _) -> inner (inner acc t1) t2
      | TyApp (t1, _, _) -> inner acc t1
      | TyLam (_, t1, _) -> inner acc t1
    in
    inner Set.Poly.empty t
  let mk_neg () = mk_con Neg
  let mk_abs () = mk_con Abs
  let mk_add () = mk_con Add
  let mk_sub () = mk_con Sub
  let mk_mul () = mk_con Mul
  let mk_div m = mk_con (Div m)
  let mk_rem m = mk_con (Rem m)
  let mk_power () = mk_con Power
  let mk_case n = mk_tyapp (mk_con (Case n))

  let sum = function
    | [] -> zero ()
    | t :: ts ->
        List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_add ()) [ t1; t2 ])

  let prod = function
    | [] -> one ()
    | t :: ts ->
        List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_mul ()) [ t1; t2 ])

  (** Observation *)

  let is_int_sort = function SInt -> true | _ -> false

  (** Evaluation *)

  let neg_sym = function
    | Add -> Sub
    | Sub -> Add
    | fsym -> failwith @@ sprintf "[IntTerm.neg_sym] %s" (str_of_sym fsym)

  let is_termlit = function IntLit _ -> true | _ -> false
  let of_termlit = function IntLit n -> mk_int n | _ -> assert false

  let assert_sort_check_of_theory sort lit =
    match (sort, lit) with SInt, IntLit _ -> () | _ -> assert false

  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory

  let eval_sym = function
    | Int n -> IntLit n
    | Neg ->
        FunLit (function IntLit x -> IntLit (Z.neg x) | _ -> assert false)
    | Abs ->
        FunLit (function IntLit x -> IntLit (Z.abs x) | _ -> assert false)
    | Add ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function IntLit y -> IntLit Z.(x + y) | _ -> assert false)
          | _ -> assert false)
    | Sub ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function IntLit y -> IntLit Z.(x - y) | _ -> assert false)
          | _ -> assert false)
    | Mul ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function IntLit y -> IntLit Z.(x * y) | _ -> assert false)
          | _ -> assert false)
    | Div m ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> IntLit (Value.div_of m x y)
                | _ -> assert false)
          | _ -> assert false)
    | Rem m ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> IntLit (Value.rem_of m x y)
                | _ -> assert false)
          | _ -> assert false)
    | Power -> failwith "not implemented"
    | Case _ -> failwith "not implemented"
    | _ -> assert false

  let eval = open_eval eval_sym of_termlit
end

module type RealTermType = sig
  include TermType

  type sym += Real of Q.t | RNeg | RAbs | RAdd | RSub | RMul | RDiv | RPower
  type Sort.t += SReal
  type termlit += RealLit of Q.t

  (** Construction *)

  val rzero : unit -> term
  val rone : unit -> term
  val mk_real : Q.t -> term
  val mk_from_float : float -> term
  val mk_rneg : unit -> term
  val mk_rabs : unit -> term
  val mk_radd : unit -> term
  val mk_rsub : unit -> term
  val mk_rmul : unit -> term
  val mk_rdiv : unit -> term
  val mk_rpower : unit -> term
  val sum : term list -> term
  val prod : term list -> term

  (** Observation *)

  val is_real_sort : Sort.t -> bool
  (** Evaluation *)

  val neg_sym : sym -> sym
end

module RealTerm : RealTermType = struct
  include Term

  type sym += Real of Q.t | RNeg | RAbs | RAdd | RSub | RMul | RDiv | RPower
  type Sort.t += SReal
  type termlit += RealLit of Q.t

  (** Sorts *)

  let rr = Sort.mk_arrow SReal SReal
  let rrr = Sort.mk_arrow SReal rr

  let sym_sort_map =
    Map.Poly.of_alist_exn
      [
        (RNeg, rr);
        (RAbs, rr);
        (RAdd, rrr);
        (RSub, rrr);
        (RMul, rrr);
        (RDiv, rrr);
        (RPower, rrr);
      ]

  let sort_of_sym = function
    | Real _ -> SReal
    | sym -> Map.Poly.find_exn sym_sort_map sym

  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)

  let str_of_sym = function
    | Real r -> sprintf "Real %s" @@ Q.to_string r
    | RNeg -> "Neg"
    | RAbs -> "Abs"
    | RAdd -> "Add"
    | RSub -> "Sub"
    | RMul -> "Mul"
    | RDiv -> "Div"
    | RPower -> "Power"
    | _ -> failwith "RealTerm.str_of_sym"

  let str_of_termlit = function RealLit r -> Q.to_string r | _ -> assert false

  let str_of_sort_theory = function
    | SReal -> "real"
    | _ -> failwith "unknown sort in RealTerm.str_of_sort_theory"

  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Construction *)

  let rzero () = mk_con (Real Q.zero)
  let rone () = mk_con (Real Q.one)
  let mk_real r = mk_con (Real r)
  let mk_from_float r = mk_con (Real (Q.of_float r))
  let mk_rneg () = mk_con RNeg
  let mk_rabs () = mk_con RAbs
  let mk_radd () = mk_con RAdd
  let mk_rsub () = mk_con RSub
  let mk_rmul () = mk_con RMul
  let mk_rdiv () = mk_con RDiv
  let mk_rpower () = mk_con RPower

  let sum = function
    | [] -> rzero ()
    | t :: ts ->
        List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_radd ()) [ t1; t2 ])

  let prod = function
    | [] -> rone ()
    | t :: ts ->
        List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_rmul ()) [ t1; t2 ])

  (** Observation *)

  let is_real_sort = function SReal -> true | _ -> false

  (** Evaluation *)

  let is_termlit = function RealLit _ -> true | _ -> false
  let of_termlit = function RealLit r -> mk_real r | _ -> assert false

  let assert_sort_check_of_theory sort lit =
    match (sort, lit) with SReal, RealLit _ -> () | _ -> assert false

  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory

  let eval_sym = function
    | Real r -> RealLit r
    | RNeg ->
        FunLit (function RealLit x -> RealLit (Q.neg x) | _ -> assert false)
    | RAbs ->
        FunLit (function RealLit x -> RealLit (Q.abs x) | _ -> assert false)
    | RAdd ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> RealLit Q.(x + y) | _ -> assert false)
          | _ -> assert false)
    | RSub ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> RealLit Q.(x - y) | _ -> assert false)
          | _ -> assert false)
    | RMul ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> RealLit Q.(x * y) | _ -> assert false)
          | _ -> assert false)
    | RDiv ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> RealLit Q.(x / y) | _ -> assert false)
          | _ -> assert false)
    | RPower -> failwith "not implemented"
    | _ -> assert false

  let eval = open_eval eval_sym of_termlit

  let neg_sym = function
    | RAdd -> RSub
    | RSub -> RAdd
    | fsym -> failwith @@ sprintf "[RealTerm.neg_sym] %s" (str_of_sym fsym)
end

module type BVTermType = sig
  include TermType

  type size = int (* bits *) option
  type signed = bool (* signed/unsigned *) option

  type sym +=
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

  type Sort.t += SBV of size

  (** Printing *)

  val str_of_size : size -> string
  val str_of_signed : signed -> string

  (** Construction *)

  val mk_bvnum : size:size -> Z.t -> term
  val mk_bvnot : size:size -> term
  val mk_bvand : size:size -> term
  val mk_bvor : size:size -> term
  val mk_bvxor : size:size -> term
  val mk_bvnand : size:size -> term
  val mk_bvnor : size:size -> term
  val mk_bvxnor : size:size -> term
  val mk_bvneg : size:size -> term
  val mk_bvadd : size:size -> term
  val mk_bvsub : size:size -> term
  val mk_bvmul : size:size -> term
  val mk_bvdiv : size:size -> signed:signed -> term
  val mk_bvrem : size:size -> signed:signed -> term
  val mk_bvsmod : size:size -> term
  val mk_bvshl : size:size -> term
  val mk_bvlshr : size:size -> term
  val mk_bvashr : size:size -> term
  val mk_bvextract : size:size -> int -> int -> term
  val mk_bvsext : size:size -> int -> term
  val mk_bvzext : size:size -> int -> term
  val mk_bvconcat : size1:size -> size2:size -> term

  (** Observation *)

  val bits_of : size -> int
  val is_signed : signed -> bool
  val is_bv_sort : Sort.t -> bool
end

module BVTerm : BVTermType = struct
  include Term

  type size = int (* bits *) option
  type signed = bool (* signed/unsigned *) option

  type sym +=
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

  type Sort.t += SBV of size

  (** Sorts *)

  let sort_of_sym = function
    | BVNum (size, _) -> SBV size
    | BVNot size | BVNeg size -> Sort.mk_arrow (SBV size) (SBV size)
    | BVEXTRACT (size, h, l) ->
        Sort.mk_arrow (SBV size) (SBV (Some (h - l + 1)))
    | BVSEXT (size, ext) | BVZEXT (size, ext) ->
        Sort.mk_arrow (SBV size)
          (SBV (match size with Some size -> Some (size + ext) | None -> None))
    | BVCONCAT (size1, size2) ->
        Sort.mk_arrow (SBV size1)
          (Sort.mk_arrow (SBV size2)
             (SBV
                (match (size1, size2) with
                | Some size1, Some size2 -> Some (size1 + size2)
                | _ -> None)))
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
    | BVASHR size ->
        Sort.mk_arrow (SBV size) (Sort.mk_arrow (SBV size) (SBV size))
    | _ -> failwith "BVTerm.sort_of_sym"

  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)

  let str_of_size = function None -> "?" | Some bits -> sprintf "%d" bits

  let str_of_signed = function
    | None -> "?"
    | Some signed -> if signed then "s" else "u"

  let str_of_sym = function
    | BVNum (_size, n) -> sprintf "Bv %s" @@ Z.to_string n
    | BVNot _size -> "BVNot"
    | BVAnd _size -> "BVAnd"
    | BVOr _size -> "BVOr"
    | BVXor _size -> "BVXor"
    | BVNand _size -> "BVNand"
    | BVNor _size -> "BVNor"
    | BVXnor _size -> "BVXnor"
    | BVNeg _size -> "BVNeg"
    | BVAdd _size -> "BVAdd"
    | BVSub _size -> "BVSub"
    | BVMul _size -> "BVMul"
    | BVDiv (_size, signed) -> sprintf "BV%sDiv" (str_of_signed signed)
    | BVRem (_size, signed) -> sprintf "BV%sRem" (str_of_signed signed)
    | BVSMod _size -> "BVSMod"
    | BVSHL _size -> "BVSHL"
    | BVLSHR _size -> "BVLSHR"
    | BVASHR _size -> "BVASHR"
    | BVEXTRACT _ -> "BVEXTRACT"
    | BVSEXT _ -> "BVSEXT"
    | BVZEXT _ -> "BVZEXT"
    | BVCONCAT _ -> "BVCONCAT"
    | _ -> failwith "BVTerm.str_of_sym"

  let str_of_sort_theory = function
    | SBV size -> sprintf "bv%s" (str_of_size size)
    | _ -> failwith "unknown sort in BVTerm.str_of_sort_theory"

  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Observation *)

  let bits_of = function None -> 32 (*ToDo*) | Some bits -> bits
  let is_signed = function None -> true (*ToDo*) | Some signed -> signed

  (** Construction *)

  let mk_bvnum ~size n = mk_con (BVNum (size, int2bv (bits_of size) n))
  let mk_bvnot ~size = mk_con (BVNot size)
  let mk_bvand ~size = mk_con (BVAnd size)
  let mk_bvor ~size = mk_con (BVOr size)
  let mk_bvxor ~size = mk_con (BVXor size)
  let mk_bvnand ~size = mk_con (BVNand size)
  let mk_bvnor ~size = mk_con (BVNor size)
  let mk_bvxnor ~size = mk_con (BVXnor size)
  let mk_bvneg ~size = mk_con (BVNeg size)
  let mk_bvadd ~size = mk_con (BVAdd size)
  let mk_bvsub ~size = mk_con (BVSub size)
  let mk_bvmul ~size = mk_con (BVMul size)
  let mk_bvdiv ~size ~signed = mk_con (BVDiv (size, signed))
  let mk_bvrem ~size ~signed = mk_con (BVRem (size, signed))
  let mk_bvsmod ~size = mk_con (BVSMod size)
  let mk_bvshl ~size = mk_con (BVSHL size)
  let mk_bvlshr ~size = mk_con (BVLSHR size)
  let mk_bvashr ~size = mk_con (BVASHR size)
  let mk_bvextract ~size h l = mk_con (BVEXTRACT (size, h, l))
  let mk_bvsext ~size ext = mk_con (BVSEXT (size, ext))
  let mk_bvzext ~size ext = mk_con (BVZEXT (size, ext))
  let mk_bvconcat ~size1 ~size2 = mk_con (BVCONCAT (size1, size2))

  (** Observation *)

  let is_bv_sort = function SBV _ -> true | _ -> false
end

module type IRBTermType = sig
  include IntTermType
  include RealTermType
  include BVTermType

  type sym += IntToReal | RealToInt | IntToBV of size | BVToInt of size * signed

  (** Construction *)

  val mk_int_to_real : unit -> term
  val mk_real_to_int : unit -> term
  val mk_int_to_bv : size:size -> term
  val mk_bv_to_int : size:size -> signed:signed -> term
end

module IRBTerm : IRBTermType = struct
  include IntTerm
  include RealTerm
  include BVTerm

  type sym += IntToReal | RealToInt | IntToBV of size | BVToInt of size * signed

  (** Sorts *)

  let ri = Sort.mk_arrow SReal SInt
  let ir = Sort.mk_arrow SInt SReal

  let sym_sort_map =
    Map.force_merge_list
      [
        Map.Poly.of_alist_exn [ (IntToReal, ir); (RealToInt, ri) ];
        IntTerm.sym_sort_map;
        RealTerm.sym_sort_map;
        BVTerm.sym_sort_map;
      ]

  let sort_of_sym = function
    | IntToBV size -> Sort.mk_arrow SInt (SBV size)
    | BVToInt (size, _) -> Sort.mk_arrow (SBV size) SInt
    | sym -> (
        try Map.Poly.find_exn sym_sort_map sym
        with exn_ when not (Common.Timer.is_async exn_) -> (
          try IntTerm.sort_of_sym sym
          with exn_ when not (Common.Timer.is_async exn_) -> (
            try RealTerm.sort_of_sym sym
            with exn_ when not (Common.Timer.is_async exn_) -> (
              try BVTerm.sort_of_sym sym
              with exn_ when not (Common.Timer.is_async exn_) ->
                failwith "IRBTerm.sort_of_sym"))))

  (** Printing *)

  let str_of_sym = function
    | IntToReal -> "IntToReal"
    | RealToInt -> "RealToInt"
    | IntToBV _ -> "IntToBV"
    | BVToInt _ -> "BVToInt"
    | sym -> (
        try IntTerm.str_of_sym sym
        with exn_ when not (Common.Timer.is_async exn_) -> (
          try RealTerm.str_of_sym sym
          with exn_ when not (Common.Timer.is_async exn_) -> (
            try BVTerm.str_of_sym sym
            with exn_ when not (Common.Timer.is_async exn_) ->
              failwith "IRBTerm.str_of_sym")))

  let str_of_termlit = function
    | IntLit n -> Z.to_string n
    | RealLit r -> Q.to_string r
    | _ -> assert false

  let str_of_sort_theory = function
    | SInt -> "int"
    | SReal -> "real"
    | SBV size -> sprintf "bv%s" (BVTerm.str_of_size size)
    | _ -> failwith "unknown sort IRBTerm.str_of_sort_theory"

  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Construction *)

  let mk_int_to_real () = mk_con IntToReal
  let mk_real_to_int () = mk_con RealToInt
  let mk_int_to_bv ~size = mk_con (IntToBV size)
  let mk_bv_to_int ~size ~signed = mk_con (BVToInt (size, signed))

  (** Evalaution *)

  let is_termlit lit = IntTerm.is_termlit lit || RealTerm.is_termlit lit

  let of_termlit lit =
    if IntTerm.is_termlit lit then IntTerm.of_termlit lit
    else if RealTerm.is_termlit lit then RealTerm.of_termlit lit
    else assert false

  let assert_sort_check_of_theory sort lit =
    match (sort, lit) with
    | SInt, IntLit _ -> ()
    | SReal, RealLit _ -> ()
    | _ -> assert false

  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory

  let eval_sym = function
    | RealToInt ->
        FunLit
          (function
          | RealLit x -> IntLit (Z.fdiv (Q.num x) (Q.den x)) (* floor *)
          | _ -> assert false)
    | IntToReal ->
        FunLit
          (function IntLit x -> RealLit (Q.of_bigint x) | _ -> assert false)
    | sym ->
        if Map.Poly.mem RealTerm.sym_sort_map sym then RealTerm.eval_sym sym
        else if Map.Poly.mem IntTerm.sym_sort_map sym then IntTerm.eval_sym sym
        else assert false

  let eval = open_eval eval_sym of_termlit
end

module type TupleTermType = sig
  include TermType

  type Sort.t += STuple of Sort.t list
  type sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int

  (** Sorts *)

  val mk_stuple : Sort.t list -> Sort.t
  val let_stuple : Sort.t -> Sort.t list

  (** Construction *)

  val mk_tuple_cons : Sort.t list -> term
  val mk_tuple_sel : Sort.t list -> int -> term
  val tuple_of : Sort.t list -> term list -> term
  val tuple_sel_of : Sort.t list -> term -> int -> term

  (** Destruction *)

  val let_tuple : term -> term list

  (** Observation *)

  val is_tuple_cons : term -> bool
  val is_tuple_sel : term -> bool
end

module TupleTerm : TupleTermType = struct
  include Term

  type Sort.t += STuple of Sort.t list
  type sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int

  (** Sorts *)

  let sort_of_sym = function
    | TupleCons sorts -> Sort.mk_fun (sorts @ [ STuple sorts ])
    | TupleSel (sorts, i) -> Sort.mk_fun (sorts @ [ List.nth_exn sorts i ])
    | _ -> failwith "TupleTerm.sort_of_sym"

  let mk_stuple sorts = STuple sorts
  let let_stuple = function STuple sorts -> sorts | _ -> assert false

  (** Printing *)

  let str_of_sym = function
    | TupleCons _ -> sprintf "tuple"
    | TupleSel (_, i) -> sprintf "tuple.%d" i
    | _ -> failwith "TupleTerm.str_of_sym"

  (** Construction *)

  let mk_tuple_cons sorts = Term.mk_con (TupleCons sorts)
  let mk_tuple_sel sorts i = Term.mk_con (TupleSel (sorts, i))
  let tuple_of sorts ts = Term.mk_apps (mk_tuple_cons sorts) ts
  let tuple_sel_of sorts term i = Term.mk_apps (mk_tuple_sel sorts i) [ term ]

  (** Destruction *)

  let let_tuple t = Term.let_apps t |> snd

  (** Observation *)

  let is_tuple_cons = function
    | App (Con (TupleCons _, _), _, _) -> true
    | _ -> false

  let is_tuple_sel = function
    | App (Con (TupleSel _, _), _, _) -> true
    | _ -> false
end

module type RefTermType = sig
  include TermType

  type Sort.t += SRef of Sort.t
  type sym += Ref of Sort.t | Deref of Sort.t | Update of Sort.t

  (** Construction *)

  val mk_ref : Sort.t -> term
  val mk_deref : Sort.t -> term
  val mk_update : Sort.t -> term
end

module RefTerm : RefTermType = struct
  include Term

  type Sort.t += SRef of Sort.t
  type sym += Ref of Sort.t | Deref of Sort.t | Update of Sort.t

  (** Construction *)

  let mk_ref sort = Term.mk_con (Ref sort)
  let mk_deref sort = Term.mk_con (Deref sort)
  let mk_update sort = Term.mk_con (Update sort)
end

module type DatatypeType = sig
  type sel = Sel of string * Sort.t | InSel of string * string * Sort.t list
  type cons = { name : string; sels : sel list }
  type func = FCons of cons | FSel of sel
  type flag = FDt | FCodt | Undef | Alias of Sort.t
  type dt = { name : string; params : Sort.t list; conses : cons list }
  type t = { name : string; dts : dt list; flag : flag }

  (** Construction *)

  val mk_dt : string -> Sort.t list -> dt
  val make : string -> dt list -> flag -> t
  val mk_uninterpreted_datatype : ?numeral:int -> string -> t
  (* val mk_cons : ?sels:sel list -> string -> cons
     val mk_sel : string -> Sort.t -> sel
     val mk_insel : string -> string -> sel *)

  (** Observation *)

  val name_of_sel : sel -> string
  val sels_of_cons : cons -> sel list
  val name_of_cons : cons -> string
  val name_of_dt : dt -> string
  val params_of_dt : dt -> Sort.t list
  val conses_of_dt : dt -> cons list
  val full_name_of_dt : (Sort.t -> string) -> dt -> string
  val dts_of : t -> dt list
  val name_of : t -> string
  val flag_of : t -> flag
  val look_up_dt : t -> string -> dt option
  val dt_of : t -> dt
  val conses_of : t -> cons list
  val params_of : t -> Sort.t list
  val full_name_of : (Sort.t -> string) -> t -> string
  val look_up_cons : t -> string -> cons option
  val look_up_sel_of_cons : cons -> string -> sel option
  val look_up_sel : t -> string -> sel option
  val look_up_func : t -> string -> func option
  val sort_of : t -> Sort.t
  val is_dt : t -> bool
  val is_codt : t -> bool
  val is_undef : t -> bool
  val is_alias : t -> bool
  val is_cons : func -> bool
  val is_sel : func -> bool

  (** Printing *)

  val str_of_sel : sel -> string
  val str_of_cons : cons -> string
  val str_of_flag : flag -> string
  val str_of : t -> string

  (** Transformation *)

  val update_name : t -> string -> t
  val update_dts : dt list -> dt -> dt list
  val update_dt : t -> dt -> t
  val update_params : t -> Sort.t list -> t
  val update_conses : t -> cons list -> t
  val add_cons : t -> cons -> t
  val add_sel : cons -> sel -> cons

  val subst_sorts :
    (Ident.svar * Sort.t -> Sort.t -> Sort.t) -> Ident.svar * Sort.t -> dt -> dt

  (** Observation *)

  val sort_of_sel : t -> sel -> Sort.t
  val sorts_of_cons_args : t -> cons -> Sort.t list
  val is_finite : t -> bool
  val is_singleton : Sort.t -> bool
  val fsym_of_cons : t -> cons -> sym
  val fsym_of_sel : t -> sel -> sym
  val fsym_of_func : t -> func -> sym
  val look_up_base_cons : t -> cons option

  (** Conversion *)

  val of_old_flag : LogicOld.Datatype.flag -> flag
  val of_old_sel : (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.sel -> sel

  val of_old_cons :
    (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.cons -> cons

  val of_old_dt : (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.dt -> dt
  val of_old : (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.t -> t
  val to_old_flag : flag -> LogicOld.Datatype.flag

  (* val to_old_sort : Sort.t -> LogicOld.Sort.t *)
  val to_old_sel : (Sort.t -> LogicOld.Sort.t) -> sel -> LogicOld.Datatype.sel

  val to_old_cons :
    (Sort.t -> LogicOld.Sort.t) -> cons -> LogicOld.Datatype.cons

  val to_old_dt : (Sort.t -> LogicOld.Sort.t) -> dt -> LogicOld.Datatype.dt
  val to_old : (Sort.t -> LogicOld.Sort.t) -> t -> LogicOld.Datatype.t
end

module type DatatypeTermType = sig
  include TermType

  type dt
  type dtcons
  type dtsel
  type flag

  type sym +=
    | DTSel of string * dt * Sort.t
    | DTCons of string * Sort.t list * dt

  type Sort.t += SDT of dt | SUS of string * Sort.t list

  (** Sorts *)

  val is_dt : Sort.t -> bool
  val is_finite_dt : ?his:Sort.t list -> Sort.t -> bool
  val is_codt : Sort.t -> bool
  val is_undef : Sort.t -> bool

  (** Construction *)

  val mk_sel : dt -> string -> term
  val mk_cons : dt -> string -> term

  val mk_dummy :
    (Sort.t -> term) -> (Sort.t -> LogicOld.Sort.t) -> Sort.t -> term

  (** Observation *)

  val is_cons : term -> bool
  val is_sel : term -> bool
  val sels_of_cons : sym -> dtsel list
end

module rec Datatype : DatatypeType = struct
  type sel = Sel of string * Sort.t | InSel of string * string * Sort.t list
  type cons = { name : string; sels : sel list }
  type func = FCons of cons | FSel of sel
  type flag = FDt | FCodt | Undef | Alias of Sort.t
  type dt = { name : string; params : Sort.t list; conses : cons list }
  type t = { name : string; dts : dt list; flag : flag }

  (** Construction *)

  let mk_dt name params = { name; params; conses = [] }
  let make name dts flag = { name; dts; flag }

  let mk_uninterpreted_datatype ?(numeral = 0) name =
    make name
      [ mk_dt name @@ List.init numeral ~f:(fun _ -> Sort.mk_fresh_svar ()) ]
      Undef

  (** Observation *)

  let name_of_sel = function Sel (name, _) | InSel (name, _, _) -> name
  let sels_of_cons (cons : cons) = cons.sels
  let name_of_cons (cons : cons) = cons.name
  let name_of_dt (dt : dt) = dt.name
  let params_of_dt (dt : dt) = dt.params
  let conses_of_dt (dt : dt) = dt.conses

  let full_name_of_dt str_of_sort dt =
    String.concat_map_list_append ~sep:", " (params_of_dt dt) ~f:str_of_sort
      (name_of_dt dt)

  let dts_of t = t.dts
  let name_of t = t.name
  let flag_of t = t.flag

  let look_up_dt t name =
    List.find ~f:(name_of_dt >> Stdlib.( = ) name) @@ dts_of t

  let dt_of t =
    match look_up_dt t @@ name_of t with Some dt -> dt | _ -> assert false

  let conses_of t = conses_of_dt @@ dt_of t
  let params_of t = params_of_dt @@ dt_of t

  let full_name_of str_of_sort t =
    String.concat_map_list_append ~sep:", " (params_of t) ~f:str_of_sort
      (name_of t)

  let look_up_cons t name =
    List.find (conses_of t) ~f:(name_of_cons >> Stdlib.( = ) name)

  let look_up_sel_of_cons cons name =
    List.find (sels_of_cons cons) ~f:(name_of_sel >> Stdlib.( = ) name)

  let look_up_sel t name =
    List.find_map (conses_of t) ~f:(Fn.flip look_up_sel_of_cons name)

  let look_up_func t name =
    match look_up_cons t name with
    | Some cons -> Some (FCons cons)
    | None -> (
        match look_up_sel t name with
        | Some sel -> Some (FSel sel)
        | None -> None)

  let sort_of t =
    match flag_of t with
    | Undef -> DatatypeTerm.SUS (name_of t, params_of t)
    | _ -> DatatypeTerm.SDT t

  let is_dt t = match flag_of t with FDt -> true | _ -> false
  let is_codt t = match flag_of t with FCodt -> true | _ -> false
  let is_undef t = match flag_of t with Undef -> true | _ -> false
  let is_alias t = match flag_of t with Alias _ -> true | _ -> false
  let is_cons = function FCons _ -> true | _ -> false
  let is_sel = function FSel _ -> true | _ -> false

  (** Printing *)

  let str_of_sel = function
    | Sel (name, ret_sort) -> sprintf "%s : %s" name (Term.str_of_sort ret_sort)
    | InSel (name, ret_name, params) ->
        sprintf "%s : %s" name
        @@ full_name_of_dt Term.str_of_sort
        @@ mk_dt ret_name params

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
        sprintf "%s %s where [%s]" (str_of_flag flag)
          (full_name_of Term.str_of_sort t)
        @@ String.concat_map_list ~sep:" and " (dts_of t) ~f:(fun dt ->
            sprintf "%s %s = %s" (str_of_flag flag)
              (full_name_of_dt Term.str_of_sort dt)
            (*String.concat_map_list ~sep:" " ~f:Term.str_of_sort @@ params_of_dt dt)*)
            @@ String.concat_map_list ~sep:" | " ~f:str_of_cons
            @@ conses_of_dt dt)

  (** Transformation *)

  let update_name t name = { t with name }

  let rec update_dts dts dt =
    match dts with
    | [] -> []
    | dt1 :: tl ->
        if String.(name_of_dt dt1 = name_of_dt dt) then dt :: tl
        else dt1 :: update_dts tl dt

  let update_dt t dt = { t with dts = update_dts (dts_of t) dt }

  let rec update_dt_params t dt params his =
    let conses' =
      List.fold2_exn (params_of_dt dt) params ~init:(conses_of_dt dt)
        ~f:(fun conses arg1 arg ->
          List.map conses ~f:(fun cons ->
              let sels' =
                List.map (sels_of_cons cons) ~f:(function
                  | Sel (name, (Sort.SVar _ as svar)) when Stdlib.(svar = arg1)
                    -> (
                      match arg with
                      | DatatypeTerm.SDT t1 -> (
                          match look_up_dt t (name_of t1) with
                          | Some _ -> InSel (name, name_of t1, params_of t1)
                          | _ -> Sel (name, arg))
                      | _ -> Sel (name, arg))
                  | InSel (name, ret_name, params) ->
                      InSel
                        ( name,
                          ret_name,
                          List.map params ~f:(fun svar ->
                              if Stdlib.(svar = arg1) then arg else svar) )
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

  and update_params t params =
    Tuple2.uncurry update_dt
    @@ update_dt_params t (dt_of t) params [ name_of t ]

  let update_conses t conses = update_dt t { (dt_of t) with conses }

  let add_cons t cons =
    let dt = dt_of t in
    update_dt t { dt with conses = cons :: conses_of_dt dt }

  let add_sel cons sel = { cons with sels = sel :: sels_of_cons cons }

  let subst_sorts subst_sort map dt =
    {
      dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            {
              cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                  | InSel (name, ret_name, params) ->
                      InSel (name, ret_name, List.map params ~f:(subst_sort map))
                  | Sel (name, ret_sort) -> Sel (name, subst_sort map ret_sort));
            });
      params = List.map (params_of_dt dt) ~f:(subst_sort map);
    }

  (** Observation *)

  let sort_of_sel t = function
    | Sel (_, sort) -> sort
    | InSel (_, ret_name, params) -> (
        match look_up_dt t ret_name with
        | Some _ -> sort_of @@ update_params (update_name t ret_name) params
        | None -> failwith @@ sprintf "unknown sort:%s" ret_name)

  let sorts_of_cons_args t cons =
    List.map (sels_of_cons cons) ~f:(sort_of_sel t)

  let is_finite t =
    not
    @@ List.exists (conses_of t) ~f:(fun cons ->
        List.for_all (sorts_of_cons_args t cons) ~f:(fun arg ->
            Stdlib.(arg = DatatypeTerm.SDT t) && DatatypeTerm.is_finite_dt arg))

  let rec is_singleton = function
    | DatatypeTerm.SDT t as sort -> (
        match conses_of t with
        | [ cons ] ->
            List.for_all (sorts_of_cons_args t cons) ~f:(fun arg ->
                Stdlib.(arg = sort) || is_singleton arg)
        | _ -> false)
    | _ -> false

  let fsym_of_cons t cons =
    (*let t = fresh_of t in*)
    match look_up_cons t @@ name_of_cons cons with
    | Some cons ->
        DatatypeTerm.DTCons (name_of_cons cons, sorts_of_cons_args t cons, t)
    | None -> assert false

  let fsym_of_sel t sel =
    (*let t = fresh_of t in*)
    match look_up_sel t @@ name_of_sel sel with
    | None -> assert false
    | Some (Sel (name, ret_sort)) -> DatatypeTerm.DTSel (name, t, ret_sort)
    | Some (InSel (name, ret_name, params)) -> (
        match look_up_dt t ret_name with
        | Some _ ->
            DatatypeTerm.DTSel
              (name, t, sort_of @@ update_params (update_name t ret_name) params)
        | None -> failwith @@ sprintf "unknown dt sort: %s" ret_name)

  let fsym_of_func t = function
    | FCons cons -> fsym_of_cons t cons
    | FSel sel -> fsym_of_sel t sel

  let look_up_base_cons t =
    let has_direct_base t =
      List.exists (conses_of t) ~f:(fun cons ->
          List.for_all (sels_of_cons cons) ~f:(function
            | Sel _ -> true
            | InSel _ -> false))
    in
    let rec look_up_other_base t his =
      if List.exists his ~f:(name_of >> Stdlib.( = ) (name_of t)) then None
      else
        List.find (conses_of t) ~f:(fun cons ->
            List.for_all (sels_of_cons cons) ~f:(function
              | Sel _ -> true
              | InSel (_, ret_name, _) ->
                  let ret_dt = update_name t ret_name in
                  if has_direct_base ret_dt then true
                  else Option.is_some @@ look_up_other_base ret_dt (t :: his)))
    in
    List.find (conses_of t) ~f:(fun cons ->
        List.for_all (sels_of_cons cons) ~f:(function
          | Sel _ -> true
          | InSel (_, ret_name, _) ->
              Option.is_some
              @@ look_up_other_base (update_name t ret_name) [ t ]))

  (*let fresh_of t =
    let dts' =
      List.map (dts_of t) ~f:(fun dt ->
          let params' = List.map (params_of_dt dt) ~f:(function Sort.SVar _ -> Sort.mk_fresh_svar () | arg -> arg) in
          snd @@ update_dt_params t dt params' [])
    in
    { t with dts = dts' }*)

  (** Conversion *)

  let rec of_old_flag = function
    | LogicOld.Datatype.FDt -> FDt
    | LogicOld.Datatype.FCodt -> FCodt
    | LogicOld.Datatype.Undef -> Undef
    | LogicOld.Datatype.Alias _ -> assert false

  and of_old_sel of_old_sort = function
    | LogicOld.Datatype.Sel (name, ret_sort) -> Sel (name, of_old_sort ret_sort)
    | LogicOld.Datatype.InSel (name, ret_name, params) ->
        InSel (name, ret_name, List.map params ~f:of_old_sort)

  and of_old_cons of_old_sort old_cons =
    let name = LogicOld.Datatype.name_of_cons old_cons in
    let sels = LogicOld.Datatype.sels_of_cons old_cons in
    { name; sels = List.map sels ~f:(of_old_sel of_old_sort) }

  and of_old_dt of_old_sort old_dt =
    let name = LogicOld.Datatype.name_of_dt old_dt in
    let conses = LogicOld.Datatype.conses_of_dt old_dt in
    let params = LogicOld.Datatype.params_of_dt old_dt in
    {
      name;
      conses = List.map conses ~f:(of_old_cons of_old_sort);
      params = List.map params ~f:of_old_sort;
    }

  and of_old of_old_sort old_t =
    let dts = LogicOld.Datatype.dts_of old_t in
    let name = LogicOld.Datatype.name_of old_t in
    let flag = LogicOld.Datatype.flag_of old_t in
    {
      name;
      flag = of_old_flag flag;
      dts = List.map dts ~f:(of_old_dt of_old_sort);
    }

  let rec to_old_flag = function
    | FDt -> LogicOld.Datatype.FDt
    | FCodt -> LogicOld.Datatype.FCodt
    | Undef -> LogicOld.Datatype.Undef
    | Alias _ -> assert false

  and to_old_sel to_old_sort = function
    | Sel (name, ret_sort) -> LogicOld.Datatype.Sel (name, to_old_sort ret_sort)
    | InSel (name, ret_name, params) ->
        LogicOld.Datatype.InSel (name, ret_name, List.map params ~f:to_old_sort)

  and to_old_cons to_old_sort cons =
    let name = name_of_cons cons in
    let sels = sels_of_cons cons |> List.map ~f:(to_old_sel to_old_sort) in
    LogicOld.Datatype.mk_cons name ~sels

  and to_old_dt to_old_sort dt =
    let name = name_of_dt dt in
    let conses = conses_of_dt dt |> List.map ~f:(to_old_cons to_old_sort) in
    let params = params_of_dt dt |> List.map ~f:to_old_sort in
    { (LogicOld.Datatype.mk_dt name params) with conses }

  and to_old to_old_sort t =
    let dts = dts_of t in
    let name = name_of t in
    let flag = flag_of t in
    LogicOld.Datatype.make name
      (List.map dts ~f:(to_old_dt to_old_sort))
      (to_old_flag flag)
end

and DatatypeTerm :
  (DatatypeTermType
    with type dt := Datatype.t
     and type dtcons := Datatype.cons
     and type dtsel := Datatype.sel
     and type flag := Datatype.flag) = struct
  include Term

  type sym +=
    | DTSel of string * Datatype.t * Sort.t
    | DTCons of string * Sort.t list * Datatype.t

  type Sort.t += SDT of Datatype.t | SUS of string * Sort.t list

  (** Sorts *)

  let sort_of_sym = function
    | DTSel (_, dt, sort) -> Sort.mk_arrow (SDT dt) sort
    | DTCons (_, sorts, dt) -> Sort.mk_fun @@ sorts @ [ SDT dt ]
    | _ -> failwith "DatatypeTerm.sort_of_sym"

  (** Printing *)

  let str_of_sym = function
    | DTSel (name, _, _) -> name
    | DTCons (name, _, _) -> name
    | _ -> failwith "DatatypeTerm.str_of_sym"

  (** Construction *)

  let mk_cons dt name =
    match Datatype.look_up_cons dt name with
    | Some cons -> Term.mk_con @@ Datatype.fsym_of_cons dt cons
    | _ -> failwith @@ "unknown cons :" ^ name

  let mk_sel dt name =
    match Datatype.look_up_sel dt name with
    | Some sel -> Term.mk_con @@ Datatype.fsym_of_sel dt sel
    | _ -> failwith @@ "unknown sel :" ^ name

  let mk_dummy f to_old_sort = function
    | SDT dt when Datatype.is_dt dt -> (
        match Datatype.look_up_base_cons dt with
        | Some cons ->
            mk_apps (mk_cons dt @@ Datatype.name_of_cons cons)
            @@ List.map ~f
            @@ Datatype.sorts_of_cons_args dt cons
        | None -> assert false)
    | SUS (name, _) as sort ->
        let name = "dummy_" ^ name in
        LogicOld.add_dummy_term (Ident.Tvar name) @@ to_old_sort sort;
        mk_var @@ Ident.Tvar name
    | sort -> f sort

  (** Observation *)

  let is_dt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_codt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_undef = function SUS (_, _) -> true | _ -> false

  let rec is_finite_dt ?(his = []) sort =
    if List.exists his ~f:(Stdlib.( = ) sort) then false
    else
      match sort with
      | SDT dt ->
          List.for_all (Datatype.conses_of dt) ~f:(fun cons ->
              Datatype.sorts_of_cons_args dt cons
              |> List.for_all ~f:(is_finite_dt ~his:(sort :: his)))
      | _ -> false

  let is_cons = function App (Con (DTCons _, _), _, _) -> true | _ -> false
  let is_sel = function App (Con (DTSel _, _), _, _) -> true | _ -> false

  let sels_of_cons = function
    | DTCons (name, _, dt) -> (
        match Datatype.look_up_cons dt name with
        | Some cons -> Datatype.sels_of_cons cons
        | _ -> assert false)
    | _ -> assert false
end

module type SeqTermType = sig
  include TermType

  (* SMT-LIB's parametric sequences, the counterpart of
     [LogicOld.T_seq]; not [LogicOld.T_trace], which is a word algebra
     over abstract symbols with no element sort. *)
  type sym +=
    | SqEmpty of Sort.t
    | SqUnit of Sort.t
    | SqConcat of Sort.t
    | SqLen of Sort.t
    | SqNth of Sort.t
    | SqExtract of Sort.t
    | SqStore of Sort.t

  type Sort.t += SSeq of Sort.t

  val elem_sort_of : Sort.t -> Sort.t
  val is_seq_sort : Sort.t -> bool
  val mk_seq_sort : Sort.t -> Sort.t
  val mk_empty : Sort.t -> term
  val mk_unit : Sort.t -> term
  val mk_concat : Sort.t -> term
  val mk_len : Sort.t -> term
  val mk_nth : Sort.t -> term
  val mk_extract : Sort.t -> term
  val mk_sq_store : Sort.t -> term
end

module SeqTerm : SeqTermType = struct
  include Term

  type sym +=
    | SqEmpty of Sort.t
    | SqUnit of Sort.t
    | SqConcat of Sort.t
    | SqLen of Sort.t
    | SqNth of Sort.t
    | SqExtract of Sort.t
    | SqStore of Sort.t

  type Sort.t += SSeq of Sort.t

  (** Sorts *)

  let sort_of_sym = function
    | SqEmpty se -> SSeq se
    | SqUnit se -> Sort.mk_fun [ se; SSeq se ]
    | SqConcat se -> Sort.mk_fun [ SSeq se; SSeq se; SSeq se ]
    | SqLen se -> Sort.mk_fun [ SSeq se; IntTerm.SInt ]
    | SqNth se -> Sort.mk_fun [ SSeq se; IntTerm.SInt; se ]
    | SqExtract se ->
        Sort.mk_fun [ SSeq se; IntTerm.SInt; IntTerm.SInt; SSeq se ]
    | SqStore se -> Sort.mk_fun [ SSeq se; IntTerm.SInt; se; SSeq se ]
    | _ -> failwith "SeqTerm.sort_of_sym"

  let elem_sort_of = function SSeq se -> se | _ -> failwith "not a seq sort"
  let is_seq_sort = function SSeq _ -> true | _ -> false

  (** Printing *)

  let str_of_sym = function
    | SqEmpty _ -> "seq.empty"
    | SqUnit _ -> "seq.unit"
    | SqConcat _ -> "seq.++"
    | SqLen _ -> "seq.len"
    | SqNth _ -> "seq.nth"
    | SqExtract _ -> "seq.extract"
    | SqStore _ -> "seq.store"
    | _ -> failwith "SeqTerm.str_of_sym"

  (** Construction *)

  let mk_seq_sort se = SSeq se
  let mk_empty se = Term.mk_con (SqEmpty se)
  let mk_unit se = Term.mk_con (SqUnit se)
  let mk_concat se = Term.mk_con (SqConcat se)
  let mk_len se = Term.mk_con (SqLen se)
  let mk_nth se = Term.mk_con (SqNth se)
  let mk_extract se = Term.mk_con (SqExtract se)
  let mk_sq_store se = Term.mk_con (SqStore se)
end

module type ArrayTermType = sig
  include TermType

  type sym +=
    | AConst of Sort.t * Sort.t
    | AStore of Sort.t * Sort.t
    | ASelect of Sort.t * Sort.t
    | ALambda of Sort.t * Sort.t

  type Sort.t += SArray of Sort.t * Sort.t

  (** Sorts *)

  val index_sort_of : Sort.t -> Sort.t
  val elem_sort_of : Sort.t -> Sort.t
  val is_array_sort : Sort.t -> bool
  val count_array_args : Sort.t -> int
  val count_array_params : term -> int
  val occurs_array_literal : term -> bool

  (** Construction *)

  val mk_array_sort : Sort.t -> Sort.t -> Sort.t
  val mk_select : Sort.t -> Sort.t -> term
  val mk_store : Sort.t -> Sort.t -> term
  val mk_const_array : Sort.t -> Sort.t -> term
  val mk_array_lambda : Sort.t -> Sort.t -> term
end

module ArrayTerm : ArrayTermType = struct
  include Term

  (* [ALambda (si, se)] turns a function into the array it denotes: applied to
     a [Bin (Lambda, x, si, body)] it is [LogicOld.T_array.ALambda]. *)
  type sym +=
    | AConst of Sort.t * Sort.t
    | AStore of Sort.t * Sort.t
    | ASelect of Sort.t * Sort.t
    | ALambda of Sort.t * Sort.t

  type Sort.t += SArray of Sort.t * Sort.t

  (** Sorts *)

  let sort_of_sym = function
    | AConst (s1, s2) -> Sort.mk_fun [ s2; SArray (s1, s2) ]
    | AStore (s1, s2) ->
        Sort.mk_fun [ SArray (s1, s2); s1; s2; SArray (s1, s2) ]
    | ASelect (s1, s2) -> Sort.mk_fun [ SArray (s1, s2); s1; s2 ]
    | ALambda (s1, s2) ->
        Sort.mk_fun [ Sort.mk_fun [ s1; s2 ]; SArray (s1, s2) ]
    | _ -> failwith "ArrayTerm.sort_of_sym"

  let index_sort_of = function
    | SArray (si, _) -> si
    | _ -> failwith "not array sort"

  let elem_sort_of = function
    | SArray (_, se) -> se
    | _ -> failwith "not array sort"

  let is_array_sort = function SArray _ -> true | _ -> false

  (* How many of a function sort's argument positions are arrays. *)
  let count_array_args s =
    let rec inner = function
      | Sort.SArrow (SArray _, c) -> 1 + inner c.val_type
      | Sort.SArrow (_, c) -> inner c.val_type
      | _ -> 0
    in
    inner s

  (* The same question of a lambda term, which is what a caller holding a
     template has rather than its sort. *)
  let count_array_params t =
    List.count (fst @@ Term.let_lam t) ~f:(snd >> is_array_sort)

  (* Does a constant array occur anywhere in this term?  An array built as a
     literal rather than read is the shape that takes a goal out of the
     fragment a first-order solver decides, so a caller may need to know
     before asking one. *)
  let occurs_array_literal t =
    let rec inner (t : term) =
      match t with
      | Con (AConst _, _) -> true
      | Con _ -> false
      | App (f, a, _) -> inner f || inner a
      | _ -> false
    in
    inner t

  (** Printing *)

  let str_of_sym = function
    | AConst _ -> "array_const"
    | AStore _ -> "store"
    | ASelect _ -> "select"
    | ALambda _ -> "array_lambda"
    | _ -> failwith "ArrayTerm.str_of_sym"

  (** Construction *)

  let mk_array_sort s1 s2 = SArray (s1, s2)
  let mk_const_array s1 s2 = Term.mk_con (AConst (s1, s2))
  let mk_store s1 s2 = Term.mk_con (AStore (s1, s2))
  let mk_select s1 s2 = Term.mk_con (ASelect (s1, s2))
  let mk_array_lambda s1 s2 = Term.mk_con (ALambda (s1, s2))
end

module type StringTermType = sig
  include TermType

  type Sort.t += SString
  type sym += StrConst of string

  (** Construction *)

  val make : string -> term

  (** Destruction *)

  val let_string_const : term -> string * info
end

module StringTerm : StringTermType = struct
  include Term

  type Sort.t += SString
  type sym += StrConst of string

  (** Sorts *)

  let sort_of_sym = function
    | StrConst _ -> SString
    | _ -> failwith "StringTerm.sort_of_sym"

  (** Printing *)

  let str_of_sym = function
    | StrConst str -> sprintf "\"%s\"" str
    | _ -> failwith "StringTerm.str_of_sym"

  (** Construction *)

  let make str = Term.mk_sym_app (StrConst str) []

  (** Destruction *)

  let let_string_const = function
    | Con (StrConst str, info) -> (str, info)
    | _ -> assert false
end

module type TraceTermType = sig
  include TermType

  type Sort.t += STrace of bool

  type sym +=
    | TrEpsilon
    | TrSymbol of string
    | TrConcat of bool
    | TrLeftQuotient of bool
    | TrRightQuotient of bool
end

module TraceTerm : TraceTermType = struct
  include Term

  type Sort.t += STrace of bool (* true: finite, false: infinite *)

  type sym +=
    | TrEpsilon
    | TrSymbol of string
    | TrConcat of bool (* the first argument must be finite *)
    | TrLeftQuotient of bool (* the first argument must be finite *)
    | TrRightQuotient of bool (* the first argument must be finite *)

  (** Sorts *)

  let sort_of_sym = function
    | TrEpsilon -> STrace true
    | TrSymbol _ev -> STrace true
    | TrConcat fin -> STrace fin
    | TrLeftQuotient fin -> STrace fin
    | TrRightQuotient fin -> STrace fin
    | _ -> failwith "TraceTerm.sort_of_sym"

  (** Printing *)

  let str_of_sym = function
    | TrEpsilon -> "eps"
    | TrSymbol ev -> ev
    | TrConcat fin -> "concat" ^ if fin then "_fin" else "_inf"
    | TrLeftQuotient _ -> "left_quot"
    | TrRightQuotient _ -> "right_quot"
    | _ -> failwith "TraceTerm.str_of_sym"
end

module type RegexTermType = sig
  include TermType

  type Sort.t += SRegEx

  type sym +=
    | RegEmpty
    | RegFull
    | RegAllChar
    | RegEpsilon
    | RegStr
    | RegComplement
    | RegStar
    | RegPlus
    | RegOpt
    | RegConcat
    | RegUnion
    | RegInter

  (** Observation *)

  val is_regex_sort : Sort.t -> bool
end

module RegexTerm : RegexTermType = struct
  include Term

  type Sort.t += SRegEx

  type sym +=
    | RegEmpty
    | RegFull
    | RegAllChar
    | RegEpsilon
    | RegStr
    | RegComplement
    | RegStar
    | RegPlus
    | RegOpt
    | RegConcat
    | RegUnion
    | RegInter

  (** Printing *)

  let str_of_sym = function
    | RegEmpty -> "empty"
    | RegFull -> "full"
    | RegAllChar -> "allchar"
    | RegEpsilon -> "eps"
    | RegStr -> "str"
    | RegComplement -> "complement"
    | RegStar -> "star"
    | RegPlus -> "plus"
    | RegOpt -> "opt"
    | RegConcat -> "concat"
    | RegUnion -> "union"
    | RegInter -> "inter"
    | _ -> failwith "RegexTermType.str_of_sym"

  (** Observation *)

  let is_regex_sort = function SRegEx -> true | _ -> false
end

module type ExtTermType = sig
  include BoolTermType
  include IRBTermType
  include TupleTermType
  include RefTermType
  include DatatypeTermType
  include ArrayTermType
  include SeqTermType
  include StringTermType
  include TraceTermType
  include RegexTermType

  type sym +=
    | Leq
    | Geq
    | Lt
    | Gt
    | PDiv
    | NotPDiv
    | RLeq
    | RGeq
    | RLt
    | RGt
    | IsInt
    | IsTuple of Sort.t list
    | NotIsTuple of Sort.t list
    | IsCons of string * Datatype.t
    | NotIsCons of string * Datatype.t
    | IsPrefix of bool
    | NotIsPrefix of bool
    | TrInRegExp of bool * string Grammar.RegWordExp.t
    | NotTrInRegExp of bool * string Grammar.RegWordExp.t
    | StrInRegExp
    | NotStrInRegExp

  val mk_dummy : Sort.t -> term

  (** Construction *)

  val mk_leq : unit -> term
  val mk_geq : unit -> term
  val mk_lt : unit -> term
  val mk_gt : unit -> term
  val mk_rleq : unit -> term
  val mk_rlt : unit -> term
  val mk_pdiv : unit -> term
  val mk_isint : unit -> term
  val mk_int_ite : unit -> term
  val mk_real_ite : unit -> term
  val mk_int_eq : unit -> term
  val mk_real_eq : unit -> term
  val mk_int_neq : unit -> term
  val mk_real_neq : unit -> term
  val mk_is_cons : string -> Datatype.t -> term
  val leq_of : term -> term -> term
  val geq_of : term -> term -> term
  val lt_of : term -> term -> term
  val gt_of : term -> term -> term
  val random_term_of : int -> Sort.t -> term

  (** Models *)

  val remove_dontcare_elem : model_elem -> term_bind
  val remove_dontcare : model -> term_bind list
  val svs_of_sym : sym -> Ident.svar_set

  val sort_reaches_svar : (Ident.svar -> bool) -> Sort.t -> bool

  val sym_may_reach_svar : sort_reaches:(Sort.t -> bool) -> sym -> bool

  val term_may_reach_svar :
    sort_reaches:(Sort.t -> bool) ->
    sym_reaches:(sym -> bool) ->
    free_var_reaches:(Ident.tvar -> bool) ->
    term ->
    bool

  (** Observation*)

  val svs_of_sort : Sort.t -> Ident.svar_set
  val sort_of : sort_env_map -> term -> Sort.t

  val head_sort_of : sort_env_map -> term -> Sort.t
  (** [head_sort_of] is [sort_of] read off the spine
      ([Term.open_head_sort_of]): the same sort wherever [sort_of] gives one. *)
  val of_old_sort : LogicOld.Sort.t -> Sort.t
  val of_old_sort_list : LogicOld.Sort.t list -> Sort.t list

  (** Conversion *)

  val of_old_sort_bind : Ident.tvar * LogicOld.Sort.t -> sort_bind
  val of_old_sort_env : LogicOld.sort_env_list -> sort_env_list
  val to_old_sort : Sort.t -> LogicOld.Sort.t

  val with_shared_datatype_conversion : (unit -> 'a) -> 'a

  val share_term_conversion : bool Atomic.t
  (** when set, [with_shared_term_conversion] opens a scope; otherwise it only
      runs its argument *)

  val share_term_conversion_terms : bool Atomic.t
  (** when set too, a scope also remembers term images, in both directions,
      and [to_old] remembers an image only when computing it drew no fresh
      name: the conversions then give, inside a scope, the values and the
      fresh-name draws they give outside one *)

  val with_shared_term_conversion : (unit -> 'a) -> 'a
  (** [with_shared_term_conversion f] runs [f] with tables, local to this
      domain and dropped when [f] returns or raises, in which [of_old_formula]
      remembers the image of every formula node it converts and [to_old_fml]
      the image of every formula-position subterm, both by physical identity;
      a node met again (physically the same value) gets the image computed the
      first time, so a set of formulas that share subformulas converts to a
      set that shares their images, at the cost of the shared part once.  The
      image is the one a conversion outside the scope gives (equal values,
      possibly more shared).  Opens a datatype scope as well. *)
  (** [with_shared_datatype_conversion f] runs [f] with the datatype tables of
      [of_old_sort] and [to_old_sort] shared across every conversion [f]
      makes in this domain, so a datatype value met again is not converted
      again; the tables are dropped when [f] returns or raises. *)
  val to_old_sort_bind : sort_bind -> Ident.tvar * LogicOld.Sort.t
  val of_old_term : LogicOld.Term.t -> term
  val of_old_atom : LogicOld.Atom.t -> term
  val of_old_formula : LogicOld.Formula.t -> term
  val of_old : LogicOld.sort_env_map * LogicOld.Formula.t -> sort_env_map * term

  val to_old_term :
    sort_env_map -> sort_env_map -> term -> term list -> LogicOld.Term.t

  val to_old_trm : sort_env_map -> sort_env_map -> term -> LogicOld.Term.t

  val to_old_atom :
    sort_env_map -> sort_env_map -> term -> term list -> LogicOld.Atom.t

  val to_old_atm : sort_env_map -> sort_env_map -> term -> LogicOld.Atom.t

  val to_old_formula :
    sort_env_map -> sort_env_map -> term -> term list -> LogicOld.Formula.t

  val to_old_fml : sort_env_map -> sort_env_map -> term -> LogicOld.Formula.t

  val sort_senv_of : sort_env_map -> sort_env_map -> sort_env_map
  (** the environment the conversion reads a subterm's sort in: the unknowns'
      and the ordinary variables' environments merged, which fails with
      [Failure "force_merge"] on a name bound at two sorts, and the defined
      functions' sorts that neither shadows; equal to [sort_senv_of_rebuilt]
      binding for binding, from caches kept per domain *)

  val sort_senv_of_rebuilt : sort_env_map -> sort_env_map -> sort_env_map

  val to_old_subst :
    sort_env_map -> sort_env_map -> term_subst_map -> LogicOld.TermSubst.t

  val str_of_formula : sort_env_map -> sort_env_map -> term -> string

  (** Printing *)

  val str_of_term : sort_env_map -> sort_env_map -> term -> string
  val simplify_formula : sort_env_map -> sort_env_map -> term -> term

  (** Transformation *)

  val simplify_term : sort_env_map -> sort_env_map -> term -> term
end

module ExtTerm :
  ExtTermType
    with type dt := Datatype.t
     and type dtcons := Datatype.cons
     and type dtsel := Datatype.sel
     and type flag := Datatype.flag = struct
  include BoolTerm
  include IRBTerm
  include TupleTerm
  include RefTerm
  include DatatypeTerm
  include ArrayTerm
  include SeqTerm
  include StringTerm
  include TraceTerm
  include RegexTerm

  type sym +=
    | Leq
    | Geq
    | Lt
    | Gt
    | PDiv
    | NotPDiv
    | RLeq
    | RGeq
    | RLt
    | RGt
    | BVLeq of size * signed
    | BVGeq of size * signed
    | BVLt of size * signed
    | BVGt of size * signed
    | IsInt
    | IsTuple of Sort.t list
    | NotIsTuple of Sort.t list
    | IsCons of string * Datatype.t
    | NotIsCons of string * Datatype.t
    | IsPrefix of bool
    | NotIsPrefix of bool
    | TrInRegExp of bool * string Grammar.RegWordExp.t
    | NotTrInRegExp of bool * string Grammar.RegWordExp.t
    | StrInRegExp
    | NotStrInRegExp

  (** Sorts *)

  let iib = Sort.mk_arrow SInt @@ Sort.mk_arrow SInt SBool
  let rrb = Sort.mk_arrow SReal @@ Sort.mk_arrow SReal SBool
  let rb = Sort.mk_arrow SReal SBool

  let sym_sort_map =
    Map.force_merge (Map.force_merge IRBTerm.sym_sort_map BoolTerm.sym_sort_map)
    @@ Map.Poly.of_alist_exn
         [
           (Leq, iib);
           (Geq, iib);
           (Lt, iib);
           (Gt, iib);
           (PDiv, iib);
           (NotPDiv, iib);
           (RLeq, rrb);
           (RGeq, rrb);
           (RLt, rrb);
           (RGt, rrb);
           (IsInt, rb);
         ]

  let sort_of_sym = function
    | BVLeq (size, _signed)
    | BVGeq (size, _signed)
    | BVLt (size, _signed)
    | BVGt (size, _signed) ->
        Sort.mk_arrow (SBV size) @@ Sort.mk_arrow (SBV size) SBool
    | IsTuple sorts | NotIsTuple sorts ->
        Sort.mk_arrow (TupleTerm.STuple sorts) BoolTerm.SBool
    | IsCons (_, dt) | NotIsCons (_, dt) ->
        Sort.mk_arrow (DatatypeTerm.SDT dt) BoolTerm.SBool
    | IsPrefix fin | NotIsPrefix fin ->
        Sort.mk_fun
          [ TraceTerm.STrace true; TraceTerm.STrace fin; BoolTerm.SBool ]
    | TrInRegExp (fin, _regexp) | NotTrInRegExp (fin, _regexp) ->
        Sort.mk_arrow (TraceTerm.STrace fin) BoolTerm.SBool
    | sym -> (
        try Map.Poly.find_exn sym_sort_map sym
        with exn_ when not (Common.Timer.is_async exn_) -> (
          try BoolTerm.sort_of_sym sym
          with exn_ when not (Common.Timer.is_async exn_) -> (
            try IRBTerm.sort_of_sym sym
            with exn_ when not (Common.Timer.is_async exn_) -> (
              try TupleTerm.sort_of_sym sym
              with exn_ when not (Common.Timer.is_async exn_) -> (
                try DatatypeTerm.sort_of_sym sym
                with exn_ when not (Common.Timer.is_async exn_) -> (
                  try ArrayTerm.sort_of_sym sym
                  with exn_ when not (Common.Timer.is_async exn_) -> (
                    try SeqTerm.sort_of_sym sym
                    with exn_ when not (Common.Timer.is_async exn_) -> (
                      try StringTerm.sort_of_sym sym
                      with exn_ when not (Common.Timer.is_async exn_) -> (
                        try TraceTerm.sort_of_sym sym
                        with exn_ when not (Common.Timer.is_async exn_) -> (
                          try RegexTerm.sort_of_sym sym
                          with exn_ when not (Common.Timer.is_async exn_) ->
                            failwith "ExtTerm.sort_of_sym"))))))))))

  let rec svs_of_sort = function
    | Sort.SVar svar -> Set.Poly.singleton svar
    | Sort.SArrow (s, c) -> Set.union (svs_of_sort s) (svs_of_triple c)
    | Sort.SForAll (svar, s1) -> Set.remove (svs_of_sort s1) svar
    | SBool | SInt | SReal | SBV _ | SString | STrace _ | SRegEx ->
        Set.Poly.empty
    | SArray (s1, s2) ->
        Set.Poly.union_list @@ List.map [ s1; s2 ] ~f:svs_of_sort
    | SSeq se -> svs_of_sort se
    | STuple sorts -> Set.Poly.union_list @@ List.map sorts ~f:svs_of_sort
    | SDT dt ->
        Set.Poly.union_list @@ List.map (Datatype.params_of dt) ~f:svs_of_sort
    | SUS (_, sorts) -> Set.Poly.union_list @@ List.map sorts ~f:svs_of_sort
    | SRef sort -> svs_of_sort sort
    | _ -> failwith "[ExtTerm.svs_of_sort] unknown sort"

  and svs_of_cont = function
    | Sort.(EVar _ | Pure) -> Set.Poly.empty
    | Sort.Eff (c1, c2) -> Set.union (svs_of_triple c1) (svs_of_triple c2)
    | _ -> failwith "[svs_of_cont]"

  and svs_of_opsig = function
    | Sort.OpSig (opmap, _) ->
        Set.Poly.union_list @@ List.map ~f:snd @@ ALMap.map opmap ~f:svs_of_sort
    | _ -> failwith "[svs_of_opsig]"

  and svs_of_triple c =
    Set.Poly.union_list
      [ svs_of_opsig c.op_sig; svs_of_sort c.val_type; svs_of_cont c.cont_eff ]

  let rec subst_sorts_cont (svar, sort) = function
    | Sort.(EVar _ | Pure) as e -> e
    | Sort.Eff (c1, c2) ->
        Sort.mk_cont_eff
          (subst_sorts_triple (svar, sort) c1)
          (subst_sorts_triple (svar, sort) c2)
    | _ -> failwith "[subst_sorts_cont]"

  and subst_sorts_sort (svar, sort) = function
    | Sort.SVar v when Stdlib.(v = svar) -> sort
    | Sort.SArrow (s, c) ->
        Sort.SArrow
          (subst_sorts_sort (svar, sort) s, subst_sorts_triple (svar, sort) c)
    | Sort.SForAll (svar', s1) ->
        if Stdlib.(svar' = svar) then Sort.SForAll (svar', s1)
        else Sort.SForAll (svar', subst_sorts_sort (svar, sort) s1)
    | (SBool | SInt | SReal | SBV _ | SString | STrace _ | SRegEx) as sort ->
        sort
    | SArray (s1, s2) ->
        SArray
          (subst_sorts_sort (svar, sort) s1, subst_sorts_sort (svar, sort) s2)
    | STuple sorts -> STuple (List.map ~f:(subst_sorts_sort (svar, sort)) sorts)
    | SDT t ->
        SDT
          (Datatype.update_dt t
          @@ Datatype.subst_sorts subst_sorts_sort (svar, sort)
               (Datatype.dt_of t))
    | SUS (name, sorts) ->
        SUS (name, List.map ~f:(subst_sorts_sort (svar, sort)) sorts)
    | SRef s -> SRef (subst_sorts_sort (svar, sort) s)
    | _ -> sort (*failwith "[subst_sorts_sort]"*)

  and subst_sorts_opsig (svar, sort) = function
    | Sort.OpSig (opmap, r) ->
        Sort.OpSig (ALMap.map opmap ~f:(subst_sorts_sort (svar, sort)), r)
    | _ -> failwith "[subst_sorts_opsig]"

  and subst_sorts_triple (svar, sort) c =
    {
      op_sig = subst_sorts_opsig (svar, sort) c.op_sig;
      val_type = subst_sorts_sort (svar, sort) c.val_type;
      cont_eff = subst_sorts_cont (svar, sort) c.cont_eff;
    }

  let svs_of_sym sym = svs_of_sort @@ sort_of_sym sym
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym
  let sort_of = Term.open_sort_of sort_of_sym subst_sorts_sort
  let head_sort_of = Term.open_head_sort_of sort_of_sym subst_sorts_sort

  (** Printing *)

  let str_of_sym = function
    | Leq -> "Leq"
    | Geq -> "Geq"
    | Lt -> "Lt"
    | Gt -> "Gt"
    | PDiv -> "PDiv"
    | NotPDiv -> "NotPDiv"
    | RLeq -> "RLeq"
    | RGeq -> "RGeq"
    | RLt -> "RLt"
    | RGt -> "RGt"
    | BVLeq _ -> "BVLeq"
    | BVGeq _ -> "BVGeq"
    | BVLt _ -> "BVLt"
    | BVGt _ -> "BVGt"
    | IsInt -> "IsInt"
    | IsTuple sorts ->
        sprintf "is_tuple(%s)"
          (String.concat_map_list ~sep:" * " sorts ~f:str_of_sort)
    | NotIsTuple sorts ->
        sprintf "is_not_tuple(%s)"
          (String.concat_map_list ~sep:" * " sorts ~f:str_of_sort)
    | IsCons (name, _) -> sprintf "is_%s" name
    | NotIsCons (name, _) -> sprintf "is_not_%s" name
    | IsPrefix _fin -> "is_prefix"
    | NotIsPrefix _fin -> "not is_prefix"
    | TrInRegExp (_fin, regexp) ->
        sprintf "in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | NotTrInRegExp (_fin, regexp) ->
        sprintf "not in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | StrInRegExp -> sprintf "str_in_regex"
    | NotStrInRegExp -> sprintf "not str_in_regex"
    | sym -> (
        try BoolTerm.str_of_sym sym
        with exn_ when not (Common.Timer.is_async exn_) -> (
          try IRBTerm.str_of_sym sym
          with exn_ when not (Common.Timer.is_async exn_) -> (
            try TupleTerm.str_of_sym sym
            with exn_ when not (Common.Timer.is_async exn_) -> (
              try DatatypeTerm.str_of_sym sym
              with exn_ when not (Common.Timer.is_async exn_) -> (
                try ArrayTerm.str_of_sym sym
                with exn_ when not (Common.Timer.is_async exn_) -> (
                  try SeqTerm.str_of_sym sym
                  with exn_ when not (Common.Timer.is_async exn_) -> (
                    try StringTerm.str_of_sym sym
                    with exn_ when not (Common.Timer.is_async exn_) -> (
                      try TraceTerm.str_of_sym sym
                      with exn_ when not (Common.Timer.is_async exn_) -> (
                        try RegexTerm.str_of_sym sym
                        with exn_ when not (Common.Timer.is_async exn_) ->
                          failwith "[ExtTerm.str_of_sym]")))))))))

  let str_of_termlit = function
    | BoolLit true -> "true"
    | BoolLit false -> "false"
    | IntLit n -> Z.to_string n
    | RealLit r -> Q.to_string r
    | _ -> assert false

  let rec str_of_sort_theory = function
    | Sort.SVar (Ident.Svar svar) -> sprintf "'%s" svar
    | Sort.SArrow (s, c) ->
        sprintf "%s -> %s%s%s"
          ((if Sort.is_arrow s || ArrayTerm.is_array_sort s then String.paren
            else Fn.id)
          @@ str_of_sort_theory s)
          (if Sort.is_empty_opsig c.op_sig then "" else "_ |> ")
          (str_of_sort_theory c.val_type)
          (if Sort.is_pure c.cont_eff then "" else " / _")
    | Sort.SForAll (Ident.Svar v, s) ->
        String.paren @@ sprintf "forall %s. %s" v (str_of_sort s)
    | SBool -> "bool"
    | SInt -> "int"
    | SReal -> "real"
    | SBV size -> sprintf "bv%s" (BVTerm.str_of_size size)
    | SString -> "string"
    | STrace true -> "fin_trace"
    | STrace false -> "inf_trace"
    | SRegEx -> "regex"
    | SSeq se -> sprintf "seq(%s)" (str_of_sort_theory se)
    | SArray (s1, s2) ->
        sprintf "%s ->> %s"
          ((if Sort.is_arrow s1 || ArrayTerm.is_array_sort s1 then String.paren
            else Fn.id)
          @@ str_of_sort_theory s1)
          (str_of_sort_theory s2)
    | STuple sorts ->
        String.paren
        @@ String.concat_map_list ~sep:" * " sorts ~f:str_of_sort_theory
    | SDT dt -> Datatype.full_name_of str_of_sort_theory dt
    | SUS (name, params) ->
        if List.is_empty params then name
        else
          sprintf "%s %s"
            (String.paren
            @@ String.concat_map_list ~sep:", " params ~f:str_of_sort_theory)
            name
    | SRef sort -> sprintf "%s ref" (String.paren @@ str_of_sort_theory sort)
    | _ -> failwith "[ExtTerm.str_of_sort_theory] unknown sort"

  let str_of_sort = (*open_str_of_sort*) str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evaluation *)

  let is_termlit = function
    | BoolTerm.BoolLit _ | IntTerm.IntLit _ | RealTerm.RealLit _ -> true
    | _ -> false

  let of_termlit lit =
    if BoolTerm.is_termlit lit then BoolTerm.of_termlit lit
    else if IntTerm.is_termlit lit then IntTerm.of_termlit lit
    else if RealTerm.is_termlit lit then RealTerm.of_termlit lit
    else assert false

  let assert_sort_check_of_theory sort lit =
    match (sort, lit) with
    | SBool, BoolLit _ -> ()
    | SInt, IntLit _ -> ()
    | SReal, RealLit _ -> ()
    | _ -> assert false

  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory

  let eval_sym = function
    | Leq ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> BoolLit Z.Compare.(x <= y)
                | _ -> assert false)
          | _ -> assert false)
    | Geq ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> BoolLit Z.Compare.(x >= y)
                | _ -> assert false)
          | _ -> assert false)
    | Lt ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> BoolLit Z.Compare.(x < y)
                | _ -> assert false)
          | _ -> assert false)
    | Gt ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> BoolLit Z.Compare.(x > y)
                | _ -> assert false)
          | _ -> assert false)
    | PDiv ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> BoolLit Z.Compare.(Z.(erem x y) = Z.zero)
                | _ -> assert false)
          | _ -> assert false)
    | NotPDiv ->
        FunLit
          (function
          | IntLit x ->
              FunLit
                (function
                | IntLit y -> BoolLit Z.Compare.(Z.(erem x y) <> Z.zero)
                | _ -> assert false)
          | _ -> assert false)
    | RLeq ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> BoolLit Q.(x <= y) | _ -> assert false)
          | _ -> assert false)
    | RGeq ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> BoolLit Q.(x >= y) | _ -> assert false)
          | _ -> assert false)
    | RLt ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> BoolLit Q.(x < y) | _ -> assert false)
          | _ -> assert false)
    | RGt ->
        FunLit
          (function
          | RealLit x ->
              FunLit
                (function RealLit y -> BoolLit Q.(x > y) | _ -> assert false)
          | _ -> assert false)
    | IsInt ->
        FunLit
          (function
          | RealLit x -> BoolLit Z.Compare.(Z.(Q.num x mod Q.den x) = Z.zero)
          | _ -> assert false)
    | sym ->
        if Map.Poly.mem BoolTerm.sym_sort_map sym then BoolTerm.eval_sym sym
        else if Map.Poly.mem IRBTerm.sym_sort_map sym then IRBTerm.eval_sym sym
        else assert false

  let eval = open_eval eval_sym of_termlit

  (** Construction *)

  let mk_leq () = mk_con Leq
  let mk_geq () = mk_con Geq
  let mk_lt () = mk_con Lt
  let mk_gt () = mk_con Gt
  let mk_pdiv () = mk_con PDiv
  let mk_not_pdiv () = mk_con NotPDiv
  let mk_rleq () = mk_con RLeq
  let mk_rgeq () = mk_con RGeq
  let mk_rlt () = mk_con RLt
  let mk_rgt () = mk_con RGt
  let mk_bvleq ~size ~signed = mk_con (BVLeq (size, signed))
  let mk_bvgeq ~size ~signed = mk_con (BVGeq (size, signed))
  let mk_bvlt ~size ~signed = mk_con (BVLt (size, signed))
  let mk_bvgt ~size ~signed = mk_con (BVGt (size, signed))
  let mk_isint () = mk_con IsInt
  let mk_int_ite () = mk_ite SInt
  let mk_real_ite () = mk_ite SReal
  let mk_int_eq () = mk_eq SInt
  let mk_real_eq () = mk_eq SReal
  let mk_int_neq () = mk_neq SInt
  let mk_real_neq () = mk_neq SReal
  let mk_is_tuple sorts = mk_con (IsTuple sorts)
  let mk_is_not_tuple sorts = mk_con (NotIsTuple sorts)
  let mk_is_cons name dt = mk_con (IsCons (name, dt))
  let mk_is_not_cons name dt = mk_con (NotIsCons (name, dt))
  let leq_of t1 t2 = mk_apps (mk_leq ()) [ t1; t2 ]
  let geq_of t1 t2 = mk_apps (mk_geq ()) [ t1; t2 ]
  let lt_of t1 t2 = mk_apps (mk_lt ()) [ t1; t2 ]
  let gt_of t1 t2 = mk_apps (mk_gt ()) [ t1; t2 ]

  (** Conversion *)

  (* Old datatype values compared by physical identity (the name is only the
     hash, since two values of one name may differ after a substitution). *)
  (* Keyed by structure, not by physical identity: type inference instantiates
     a parametric datatype afresh at every occurrence, so an input's formulas
     hold many physically distinct but equal copies of one instance, and a
     table that tells them apart converts each copy again and keeps them all
     in one bucket of their common name, which a shared scope then walks at
     every lookup.  [Stdlib.compare] skips the physically shared parts of two
     copies, which is most of them; the hash reads a bounded prefix of the
     value, so equal values hash alike and a lookup costs no walk of the whole
     datatype. *)
  module OldDtPhysTbl = Stdlib.Hashtbl.Make (struct
    type t = LogicOld.Datatype.t

    let equal dt1 dt2 = phys_equal dt1 dt2 || Stdlib.compare dt1 dt2 = 0
    let hash (t : LogicOld.Datatype.t) = Stdlib.Hashtbl.hash t
  end)

  (* The sort conversion carries a table from each datatype value already
     converted to its image, created at the first datatype met and local to
     one top-level call.  A datatype value holds every selector's sort, and
     such a sort holds the datatype it returns, so the datatypes of an input
     form a graph whose values are shared; converting each occurrence afresh
     unfolds that graph into a tree, exponential in its depth when datatypes
     refer to each other with fan-out (a front end's monomorphised wrappers
     nested a few levels deep), and on an input with a few hundred such
     datatypes the unfolded copies exhausted memory.  With the table each
     shared value is converted once per call and its image is shared the
     same way.  The result is the same value either way: the conversion is a
     function of its argument, so a remembered image equals a recomputed
     one. *)
  (* New datatype values keyed by structure, the reverse of the table
     [of_old_sort_in] keeps and for the same reasons: a sort computed from a
     selector or a constructor builds a fresh copy of its datatype, so one
     formula holds many physically distinct copies of one instance, and a
     physical table shared across a whole problem kept them all in the bucket
     of their common name. *)
  module NewDtPhysTbl = Stdlib.Hashtbl.Make (struct
    type t = Datatype.t

    let equal dt1 dt2 = phys_equal dt1 dt2 || Stdlib.compare dt1 dt2 = 0
    let hash (t : Datatype.t) = Stdlib.Hashtbl.hash t
  end)

  (* [sort_reaches_svar keys s] is [true] when a sort variable satisfying
     [keys] occurs in [s], datatype declarations included: every member of a
     datatype's group, its parameters, every selector's sort, an alias's sort,
     and the datatypes those contain, each datatype value visited once (by
     physical identity).  It over-approximates: a variable bound by [SForAll]
     counts, and a sort constructor this walk does not know answers [true].
     So [false] licenses reading a substitution of those variables as the
     identity on [s]. *)
  let sort_reaches_svar keys root =
    let visited = NewDtPhysTbl.create 16 in
    let exception Found in
    let rec sort = function
      | Sort.SVar svar -> if keys svar then raise Found
      | Sort.SArrow (s, c) ->
          sort s;
          triple c
      | Sort.SForAll (_, s) -> sort s
      | SBool | SInt | SReal | SBV _ | SString | STrace _ | SRegEx -> ()
      | SArray (s1, s2) ->
          sort s1;
          sort s2
      | SSeq se -> sort se
      | STuple sorts -> List.iter sorts ~f:sort
      | SDT dt -> datatype dt
      | SUS (_, args) -> List.iter args ~f:sort
      | SRef s -> sort s
      | _ -> raise Found
    and triple (c : Sort.c) =
      (match c.op_sig with
      | Sort.OpSig (opmap, _) -> List.iter opmap ~f:(fun (_, s) -> sort s)
      | _ -> raise Found);
      sort c.val_type;
      match c.cont_eff with
      | Sort.Eff (c1, c2) ->
          triple c1;
          triple c2
      | Sort.(EVar _ | Pure) -> ()
      | _ -> raise Found
    and datatype (t : Datatype.t) =
      if not (NewDtPhysTbl.mem visited t) then (
        NewDtPhysTbl.add visited t ();
        (match t.flag with Datatype.Alias s -> sort s | _ -> ());
        List.iter t.dts ~f:(fun (d : Datatype.dt) ->
            List.iter d.params ~f:sort;
            List.iter d.conses ~f:(fun (cons : Datatype.cons) ->
                List.iter cons.sels ~f:(function
                  | Datatype.Sel (_, s) -> sort s
                  | Datatype.InSel (_, _, args) -> List.iter args ~f:sort))))
    in
    try
      sort root;
      false
    with Found -> true

  (* [sym_may_reach_svar ~sort_reaches sym]: [sort_reaches] of the symbol's
     sort as [sort_of_sym] gives it, and [true] for a symbol it cannot type *)
  let sym_may_reach_svar ~sort_reaches sym =
    match sort_of_sym sym with
    | s -> sort_reaches s
    | exception exn_ when not (Common.Timer.is_async exn_) -> true

  (* [term_may_reach_svar ~sort_reaches ~sym_reaches ~free_var_reaches t]
     over-approximates whether a sort that [sort_reaches] holds of occurs in
     [t]: in a binder's or a [let]'s sort, a type application's sort, a symbol
     ([sym_reaches], which is to be [sym_may_reach_svar] or a memo of it), or,
     for a variable not bound inside [t], whatever [free_var_reaches] says of
     it.  A type abstraction counts as reaching.  So [false] means no sort the
     term mentions, nor any free variable's, reaches one. *)
  let term_may_reach_svar ~sort_reaches ~sym_reaches ~free_var_reaches term =
    let rec aux bound = function
      | Var (x, _) -> (not (Set.mem bound x)) && free_var_reaches x
      | Con (sym, _) -> sym_reaches sym
      | App (t1, t2, _) -> aux bound t1 || aux bound t2
      | Bin (_, x, s, t, _) -> sort_reaches s || aux (Set.add bound x) t
      | Let (x, s, d, b, _) ->
          sort_reaches s || aux bound d || aux (Set.add bound x) b
      | TyApp (t, s, _) -> sort_reaches s || aux bound t
      | TyLam _ -> true
    in
    aux Set.Poly.empty term

  (* A scope in which the sort conversions in both directions share their
     datatype tables across calls: a formula mentions the same datatype sort
     at every variable and every constructor it holds, and without a shared
     table each occurrence converted the whole graph of datatypes it reaches
     again.  The tables live in domain-local storage for the dynamic extent of
     one [with_shared_datatype_conversion] and are dropped when it returns or
     raises, so nothing outlives the call that asked for it and two domains
     never share one; a nested scope reuses the enclosing tables.  Sharing
     changes no result, since each conversion is a function of its argument
     and datatype values are immutable. *)
  type dt_conversion_tables = {
    of_old_tbl : Datatype.t OldDtPhysTbl.t;
    to_old_tbl : LogicOld.Datatype.t NewDtPhysTbl.t;
  }

  let dt_conversion_scope : dt_conversion_tables option Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  let with_shared_datatype_conversion f =
    match Domain.DLS.get dt_conversion_scope with
    | Some _ -> f ()
    | None ->
        Domain.DLS.set dt_conversion_scope
          (Some
             {
               of_old_tbl = OldDtPhysTbl.create 64;
               to_old_tbl = NewDtPhysTbl.create 64;
             });
        Exn.protect ~f ~finally:(fun () ->
            Domain.DLS.set dt_conversion_scope None)

  (* Physical tables for the term conversions.  A clausal form that
     multiplies alternatives builds thousands of clauses whose pure parts are
     disjunctions of the same physical subformulas; converting each clause
     separately copied every shared subformula once per clause, so a set that
     took a few megabytes as built took gigabytes after one round trip
     between the two representations, and every later pass walked and copied
     the gigabytes.  Keys are compared by physical identity only: equal but
     distinct values are converted separately (structural comparison would
     walk them, and datatype values inside sorts make that walk costly).  The
     hash is the address ([Common.Ext.Hashtbl.phys_hash]): a structural hash
     spends its budget inside the sorts, so the nodes of a multiplied clausal
     form fell into a few buckets and the conversion spent minutes walking
     them. *)
  module OldFmlPhysTbl = Stdlib.Hashtbl.Make (struct
    type t = LogicOld.Formula.t

    let equal = phys_equal
    let hash = Common.Ext.Hashtbl.phys_hash
  end)

  module TermPhysTbl = Stdlib.Hashtbl.Make (struct
    type t = term

    let equal = phys_equal
    let hash = Common.Ext.Hashtbl.phys_hash
  end)

  (* [to_old] reads, besides the term, the two sort environments (and the
     process-global dummy and function environments, which no conversion
     changes): an image is reused under another environment only when the
     existential environment is the same value and every variable occurring
     in the term, bound or free, has the same sort, or none, in both universal
     environments.  Comparing the bound ones too is a superset of what the
     conversion reads, so it costs only reuse, never correctness. *)
  type to_old_entry = {
    entry_exi : sort_env_map;
    entry_uni : sort_env_map;
    entry_img : LogicOld.Formula.t;
  }

  (* With this set as well, a scope of [with_shared_term_conversion] also
     remembers the image of every term: [of_old_term] by the old term's
     physical identity, and [to_old_trm] (the conversion of a term in term
     position) by the term's physical identity under the same reuse test as
     the formula entries.  And every image of [to_old] -- formula or term --
     is remembered only when its conversion drew no fresh name (the
     conversion of a beta-redex substitutes, and the substitution renames
     binders), so that a hit skips no draw the conversion outside a scope
     would make.  With it, a conversion inside a scope gives the value one
     outside gives, with the same fresh-name draws; only the sharing differs.
     Why: a clausal product repeats large terms (an argument tuple, a
     datatype value) in many atoms, and the formula entries alone converted
     each repetition again -- 2.3 million old nodes became 50 million. *)
  let share_term_conversion_terms : bool Atomic.t = Atomic.make false

  module OldTermPhysTbl = Stdlib.Hashtbl.Make (struct
    type t = LogicOld.Term.t

    let equal = phys_equal
    let hash = Common.Ext.Hashtbl.phys_hash
  end)

  type to_old_term_entry = {
    tentry_exi : sort_env_map;
    tentry_uni : sort_env_map;
    tentry_img : LogicOld.Term.t;
  }

  type term_conversion_tables = {
    of_old_fml_tbl : term OldFmlPhysTbl.t;
    to_old_fml_tbl : to_old_entry list TermPhysTbl.t;
    vars_tbl : Ident.tvar Set.Poly.t TermPhysTbl.t;
    of_old_term_tbl : term OldTermPhysTbl.t;
    to_old_term_tbl : to_old_term_entry list TermPhysTbl.t;
  }

  let share_term_conversion : bool Atomic.t = Atomic.make false


  let term_conversion_scope : term_conversion_tables option Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  let with_shared_term_conversion f =
    if not (Atomic.get share_term_conversion) then f ()
    else
      match Domain.DLS.get term_conversion_scope with
      | Some _ -> f ()
      | None ->
          Domain.DLS.set term_conversion_scope
            (Some
               {
                 of_old_fml_tbl = OldFmlPhysTbl.create 1024;
                 to_old_fml_tbl = TermPhysTbl.create 1024;
                 vars_tbl = TermPhysTbl.create 1024;
                 of_old_term_tbl = OldTermPhysTbl.create 1024;
                 to_old_term_tbl = TermPhysTbl.create 1024;
               });
          Exn.protect
            ~f:(fun () -> with_shared_datatype_conversion f)
            ~finally:(fun () -> Domain.DLS.set term_conversion_scope None)

  (* every variable name occurring in [t], bound or free, remembered by
     physical identity at application nodes so that a shared subterm is read
     once *)
  let rec vars_occurring tbls t =
    match t with
    | Var (x, _) -> Set.Poly.singleton x
    | Con _ -> Set.Poly.empty
    | App (t1, t2, _) -> (
        match TermPhysTbl.find_opt tbls.vars_tbl t with
        | Some vs -> vs
        | None ->
            let vs =
              Set.union (vars_occurring tbls t1) (vars_occurring tbls t2)
            in
            TermPhysTbl.add tbls.vars_tbl t vs;
            vs)
    | Bin (_, x, _, t1, _) -> Set.add (vars_occurring tbls t1) x
    | Let (x, _, t1, t2, _) ->
        Set.add
          (Set.union (vars_occurring tbls t1) (vars_occurring tbls t2))
          x
    | TyApp (t1, _, _) | TyLam (_, t1, _) -> vars_occurring tbls t1

  let sort_opt_equal s1 s2 =
    match (s1, s2) with
    | None, None -> true
    | Some s1, Some s2 -> phys_equal s1 s2 || Stdlib.compare s1 s2 = 0
    | _ -> false

  let to_old_reusable_in tbls exi_senv uni_senv term entry_exi entry_uni =
    phys_equal entry_exi exi_senv
    && (phys_equal entry_uni uni_senv
       || Set.for_all (vars_occurring tbls term) ~f:(fun x ->
           sort_opt_equal
             (Map.Poly.find uni_senv x)
             (Map.Poly.find entry_uni x)))

  let to_old_reusable tbls exi_senv uni_senv term entry =
    to_old_reusable_in tbls exi_senv uni_senv term entry.entry_exi
      entry.entry_uni

  (* at most this many environments are kept per term: the entries of one
     key are tried in turn, so the list bounds the cost of a miss *)
  let to_old_entries_per_term = 4

  let rec of_old_cont_in tbl = function
    | LogicOld.Sort.EVar x -> Sort.EVar x
    | LogicOld.Sort.Pure -> Sort.Pure
    | LogicOld.Sort.Eff (c1, c2) ->
        Sort.mk_cont_eff (of_old_triple_in tbl c1) (of_old_triple_in tbl c2)
    | _ -> failwith "[of_old_cont]"

  and of_old_sort_in tbl = function
    | LogicOld.Sort.SVar svar -> Sort.SVar svar
    | LogicOld.Sort.SArrow (s, c) ->
        Sort.SArrow (of_old_sort_in tbl s, of_old_triple_in tbl c)
    | LogicOld.T_bool.SBool -> SBool
    | LogicOld.T_int.SInt -> SInt
    | LogicOld.T_real.SReal -> SReal
    | LogicOld.T_bv.SBV size -> SBV size
    | LogicOld.T_string.SString -> SString
    | LogicOld.T_trace.STrace fin -> STrace fin
    | LogicOld.T_regex.SRegEx -> SRegEx
    | LogicOld.T_array.SArray (s1, s2) ->
        SArray (of_old_sort_in tbl s1, of_old_sort_in tbl s2)
    | LogicOld.T_seq.SSeq se -> SSeq (of_old_sort_in tbl se)
    | LogicOld.T_tuple.STuple sorts ->
        STuple (List.map sorts ~f:(of_old_sort_in tbl))
    | LogicOld.T_dt.SDT dt -> (
        let tbl =
          match (tbl, Domain.DLS.get dt_conversion_scope) with
          | Some tbl, _ -> tbl
          | None, Some scope -> scope.of_old_tbl
          | None, None -> OldDtPhysTbl.create 16
        in
        match OldDtPhysTbl.find_opt tbl dt with
        | Some dt' -> SDT dt'
        | None ->
            let dt' = Datatype.of_old (of_old_sort_in (Some tbl)) dt in
            OldDtPhysTbl.add tbl dt dt';
            SDT dt')
    | LogicOld.T_dt.SUS (name, args) ->
        SUS (name, List.map args ~f:(of_old_sort_in tbl))
    | LogicOld.T_ref.SRef sort -> SRef (of_old_sort_in tbl sort)
    | sort ->
        failwith @@ "unsupported old sort: " ^ LogicOld.Term.str_of_sort sort

  and of_old_opsig_in tbl = function
    | LogicOld.Sort.OpSig (opmap, rv) ->
        Sort.OpSig (ALMap.map opmap ~f:(of_old_sort_in tbl), rv)
    | _ -> failwith "[of_old_opsig]"

  and of_old_triple_in tbl (c : LogicOld.Sort.c) : Sort.c =
    {
      op_sig = of_old_opsig_in tbl c.op_sig;
      val_type = of_old_sort_in tbl c.val_type;
      cont_eff = of_old_cont_in tbl c.cont_eff;
    }

  let of_old_sort = of_old_sort_in None

  let of_old_sort_list = List.map ~f:of_old_sort
  let of_old_sort_bind (x, s) = (x, of_old_sort s)
  let of_old_sort_env = List.map ~f:of_old_sort_bind
  let of_unop = function LogicOld.Formula.Not -> mk_not ()

  let of_binop = function
    | LogicOld.Formula.And -> mk_and ()
    | LogicOld.Formula.Or -> mk_or ()
    | LogicOld.Formula.Imply -> mk_imply ()
    | LogicOld.Formula.Iff -> mk_iff ()
    | LogicOld.Formula.Xor -> mk_xor ()

  let rec of_old_fun_sym sym sargs =
    match (sym, sargs) with
    | LogicOld.FVar (x, _, _), _ -> mk_var x
    | LogicOld.T_bool.Formula phi, [] -> of_old_formula phi
    | LogicOld.T_bool.IfThenElse, [ _; sort; _ ] -> mk_ite sort
    | LogicOld.T_int.Int n, [] -> mk_int n
    | LogicOld.T_int.Neg, [ _ ] -> mk_neg ()
    | LogicOld.T_int.Abs, [ _ ] -> mk_abs ()
    | LogicOld.T_int.Add, [ _; _ ] -> mk_add ()
    | LogicOld.T_int.Sub, [ _; _ ] -> mk_sub ()
    | LogicOld.T_int.Mul, [ _; _ ] -> mk_mul ()
    | LogicOld.T_int.Div m, [ _; _ ] -> mk_div m
    | LogicOld.T_int.Rem m, [ _; _ ] -> mk_rem m
    | LogicOld.T_int.Power, [ _; _ ] -> mk_power ()
    | LogicOld.T_int.Case n, _ :: sort :: _ -> mk_case n sort
    | LogicOld.T_real.Real r, [] -> mk_real r
    | LogicOld.T_real.RNeg, [ _ ] -> mk_rneg ()
    | LogicOld.T_real.RAbs, [ _ ] -> mk_rabs ()
    | LogicOld.T_real.RAdd, [ _; _ ] -> mk_radd ()
    | LogicOld.T_real.RSub, [ _; _ ] -> mk_rsub ()
    | LogicOld.T_real.RMul, [ _; _ ] -> mk_rmul ()
    | LogicOld.T_real.RDiv, [ _; _ ] -> mk_rdiv ()
    | LogicOld.T_real.RPower, [ _; _ ] -> mk_rpower ()
    | LogicOld.T_bv.BVNum (size, n), [] -> mk_bvnum ~size n
    | LogicOld.T_bv.BVNot size, [ _ ] -> mk_bvnot ~size
    | LogicOld.T_bv.BVAnd size, [ _; _ ] -> mk_bvand ~size
    | LogicOld.T_bv.BVOr size, [ _; _ ] -> mk_bvor ~size
    | LogicOld.T_bv.BVXor size, [ _; _ ] -> mk_bvxor ~size
    | LogicOld.T_bv.BVNand size, [ _; _ ] -> mk_bvnand ~size
    | LogicOld.T_bv.BVNor size, [ _; _ ] -> mk_bvnor ~size
    | LogicOld.T_bv.BVXnor size, [ _; _ ] -> mk_bvxnor ~size
    | LogicOld.T_bv.BVNeg size, [ _ ] -> mk_bvneg ~size
    | LogicOld.T_bv.BVAdd size, [ _; _ ] -> mk_bvadd ~size
    | LogicOld.T_bv.BVSub size, [ _; _ ] -> mk_bvsub ~size
    | LogicOld.T_bv.BVMul size, [ _; _ ] -> mk_bvmul ~size
    | LogicOld.T_bv.BVDiv (size, signed), [ _; _ ] -> mk_bvdiv ~size ~signed
    | LogicOld.T_bv.BVRem (size, signed), [ _; _ ] -> mk_bvrem ~size ~signed
    | LogicOld.T_bv.BVSMod size, [ _; _ ] -> mk_bvsmod ~size
    | LogicOld.T_bv.BVSHL size, [ _; _ ] -> mk_bvshl ~size
    | LogicOld.T_bv.BVLSHR size, [ _; _ ] -> mk_bvlshr ~size
    | LogicOld.T_bv.BVASHR size, [ _; _ ] -> mk_bvashr ~size
    | LogicOld.T_bv.BVEXTRACT (size, h, l), [ _ ] -> mk_bvextract ~size h l
    | LogicOld.T_bv.BVSEXT (size, ext), [ _ ] -> mk_bvsext ~size ext
    | LogicOld.T_bv.BVZEXT (size, ext), [ _ ] -> mk_bvzext ~size ext
    | LogicOld.T_bv.BVCONCAT (size1, size2), [ _; _ ] ->
        mk_bvconcat ~size1 ~size2
    | LogicOld.T_irb.IntToReal, [ _ ] -> mk_int_to_real ()
    | LogicOld.T_irb.RealToInt, [ _ ] -> mk_real_to_int ()
    | LogicOld.T_irb.IntToBV size, [ _ ] -> mk_int_to_bv ~size
    | LogicOld.T_irb.BVToInt (size, signed), [ _ ] -> mk_bv_to_int ~size ~signed
    (*| LogicOld.T_num.NNeg svar, [_] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.Value (_, svar), [] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NAdd svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NSub svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NMul svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NDiv svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NRem svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NPower svar, [_; _] -> failwith "of_old_fun_sym"
    *)
    | LogicOld.T_string.StrConst str, _ -> mk_con @@ StrConst str
    | LogicOld.T_trace.TrEpsilon, _ -> mk_con TrEpsilon
    | LogicOld.T_trace.TrSymbol ev, _ -> mk_con @@ TrSymbol ev
    | LogicOld.T_trace.TrConcat fin, _ -> mk_con @@ TrConcat fin
    | LogicOld.T_trace.TrLeftQuotient fin, _ -> mk_con @@ TrLeftQuotient fin
    | LogicOld.T_trace.TrRightQuotient fin, _ -> mk_con @@ TrRightQuotient fin
    | LogicOld.T_regex.RegEmpty, _ -> mk_con RegEmpty
    | LogicOld.T_regex.RegFull, _ -> mk_con RegFull
    | LogicOld.T_regex.RegAllChar, _ -> mk_con RegAllChar
    | LogicOld.T_regex.RegEpsilon, _ -> mk_con RegEpsilon
    | LogicOld.T_regex.RegStr, _ -> mk_con @@ RegStr
    | LogicOld.T_regex.RegComplement, _ -> mk_con RegComplement
    | LogicOld.T_regex.RegStar, _ -> mk_con RegStar
    | LogicOld.T_regex.RegPlus, _ -> mk_con RegPlus
    | LogicOld.T_regex.RegOpt, _ -> mk_con RegOpt
    | LogicOld.T_regex.RegConcat, _ -> mk_con RegConcat
    | LogicOld.T_regex.RegUnion, _ -> mk_con RegUnion
    | LogicOld.T_regex.RegInter, _ -> mk_con RegInter
    | LogicOld.T_array.AConst (s1, s2), _ ->
        mk_const_array (of_old_sort s1) (of_old_sort s2)
    | LogicOld.T_array.AStore (s1, s2), _ ->
        mk_store (of_old_sort s1) (of_old_sort s2)
    | LogicOld.T_array.ASelect (s1, s2), _ ->
        mk_select (of_old_sort s1) (of_old_sort s2)
    | LogicOld.T_seq.SqEmpty se, _ -> mk_empty (of_old_sort se)
    | LogicOld.T_seq.SqUnit se, _ -> mk_unit (of_old_sort se)
    | LogicOld.T_seq.SqConcat se, _ -> mk_concat (of_old_sort se)
    | LogicOld.T_seq.SqLen se, _ -> mk_len (of_old_sort se)
    | LogicOld.T_seq.SqNth se, _ -> mk_nth (of_old_sort se)
    | LogicOld.T_seq.SqExtract se, _ -> mk_extract (of_old_sort se)
    | LogicOld.T_seq.SqStore se, _ -> mk_sq_store (of_old_sort se)
    | LogicOld.T_tuple.TupleCons sorts, _ ->
        mk_tuple_cons (of_old_sort_list sorts)
    | LogicOld.T_tuple.TupleSel (sorts, i), _ ->
        mk_tuple_sel (of_old_sort_list sorts) i
    | LogicOld.T_dt.DTCons (name, _, dt), _ ->
        mk_cons (Datatype.of_old of_old_sort dt) name
    | LogicOld.T_dt.DTSel (name, dt, _), _ ->
        mk_sel (Datatype.of_old of_old_sort dt) name
    | LogicOld.T_ref.Ref sort, [ _ ] -> mk_ref (of_old_sort sort)
    | LogicOld.T_ref.Deref sort, [ _ ] -> mk_deref (of_old_sort sort)
    | LogicOld.T_ref.Update sort, [ _; _ ] -> mk_update (of_old_sort sort)
    | _ ->
        failwith
        @@ sprintf "[Logic.of_old_fun_sym] %s not supported"
             (LogicOld.Term.str_of_funsym sym)

  and of_old_pred_sym sym sargs =
    match (sym, sargs) with
    | LogicOld.T_bool.Eq, [ sort; _ ] -> mk_eq sort
    | LogicOld.T_bool.Neq, [ sort; _ ] -> mk_neq sort
    | LogicOld.T_int.Leq, [ _; _ ] -> mk_leq ()
    | LogicOld.T_int.Geq, [ _; _ ] -> mk_geq ()
    | LogicOld.T_int.Lt, [ _; _ ] -> mk_lt ()
    | LogicOld.T_int.Gt, [ _; _ ] -> mk_gt ()
    | LogicOld.T_int.PDiv, [ _; _ ] -> mk_pdiv ()
    | LogicOld.T_int.NotPDiv, [ _; _ ] -> mk_not_pdiv ()
    | LogicOld.T_real.RLeq, [ _; _ ] -> mk_rleq ()
    | LogicOld.T_real.RGeq, [ _; _ ] -> mk_rgeq ()
    | LogicOld.T_real.RLt, [ _; _ ] -> mk_rlt ()
    | LogicOld.T_real.RGt, [ _; _ ] -> mk_rgt ()
    | LogicOld.T_bv.BVLeq (size, signed), [ _; _ ] -> mk_bvleq ~size ~signed
    | LogicOld.T_bv.BVGeq (size, signed), [ _; _ ] -> mk_bvgeq ~size ~signed
    | LogicOld.T_bv.BVLt (size, signed), [ _; _ ] -> mk_bvlt ~size ~signed
    | LogicOld.T_bv.BVGt (size, signed), [ _; _ ] -> mk_bvgt ~size ~signed
    | LogicOld.T_irb.IsInt, [ _ ] -> mk_isint ()
    | LogicOld.T_num.NLeq svar, [ _; _ ] ->
        mk_tyapp (mk_con Leq) (Sort.SVar svar)
    | LogicOld.T_num.NGeq svar, [ _; _ ] ->
        mk_tyapp (mk_con Geq) (Sort.SVar svar)
    | LogicOld.T_num.NLt svar, [ _; _ ] -> mk_tyapp (mk_con Lt) (Sort.SVar svar)
    | LogicOld.T_num.NGt svar, [ _; _ ] -> mk_tyapp (mk_con Gt) (Sort.SVar svar)
    | LogicOld.T_trace.IsPrefix fin, [ _; _ ] -> Term.mk_con @@ IsPrefix fin
    | LogicOld.T_trace.NotIsPrefix fin, [ _; _ ] ->
        Term.mk_con @@ NotIsPrefix fin
    | LogicOld.T_trace.TrInRegExp (fin, regexp), [ _ ] ->
        Term.mk_con @@ TrInRegExp (fin, regexp)
    | LogicOld.T_trace.NotTrInRegExp (fin, regexp), [ _ ] ->
        Term.mk_con @@ NotTrInRegExp (fin, regexp)
    (* [str.in.re s R] is binary (the string and the regex term); with [[ _ ]]
       these arms never matched and every string-regex atom fell to the
       catch-all "not supported" *)
    | LogicOld.T_regex.StrInRegExp, [ _; _ ] -> Term.mk_con StrInRegExp
    | LogicOld.T_regex.NotStrInRegExp, [ _; _ ] -> Term.mk_con NotStrInRegExp
    | LogicOld.T_tuple.IsTuple sorts, _ -> mk_is_tuple (of_old_sort_list sorts)
    | LogicOld.T_tuple.NotIsTuple sorts, _ ->
        mk_is_not_tuple (of_old_sort_list sorts)
    | LogicOld.T_dt.IsCons (name, dt), _ ->
        mk_is_cons name (Datatype.of_old of_old_sort dt)
    | LogicOld.T_dt.NotIsCons (name, dt), _ ->
        mk_is_not_cons name (Datatype.of_old of_old_sort dt)
    | _ ->
        failwith
        @@ sprintf "[Logic.of_old_pred_sym] %s not supported"
        @@ LogicOld.Predicate.str_of_psym sym

  and of_old_term t =
    match Domain.DLS.get term_conversion_scope with
    | Some tbls when Atomic.get share_term_conversion_terms -> (
        match OldTermPhysTbl.find_opt tbls.of_old_term_tbl t with
        | Some t' -> t'
        | None ->
            let t' = of_old_term_node t in
            OldTermPhysTbl.add tbls.of_old_term_tbl t t';
            t')
    | _ -> of_old_term_node t

  and of_old_term_node = function
    | LogicOld.Term.Var (tvar, _sort, _) -> mk_var tvar
    | LogicOld.Term.FunApp (LogicOld.T_array.ALambda ((x, si), se), [ body ], _)
      ->
        let si = of_old_sort si in
        mk_app (mk_array_lambda si (of_old_sort se))
        @@ mk_bind Lambda x si (of_old_term body)
    | LogicOld.Term.FunApp (sym, args, _) ->
        let sargs = List.map args ~f:(LogicOld.Term.sort_of >> of_old_sort) in
        mk_apps (of_old_fun_sym sym sargs) (List.map ~f:of_old_term args)
    | LogicOld.Term.LetTerm (var, sort, def, body, _) ->
        mk_let var (of_old_sort sort) (of_old_term def) (of_old_term body)

  and of_old_atom = function
    | LogicOld.Atom.True _ -> mk_bool true
    | LogicOld.Atom.False _ -> mk_bool false
    | LogicOld.Atom.App (LogicOld.Predicate.Var (Ident.Pvar pvar, _), args, _)
      ->
        mk_apps (mk_var (Ident.Tvar pvar)) (List.map ~f:of_old_term args)
    | LogicOld.Atom.App (LogicOld.Predicate.Psym psym, args, _) ->
        let sargs = List.map args ~f:(LogicOld.Term.sort_of >> of_old_sort) in
        mk_apps (of_old_pred_sym psym sargs) (List.map ~f:of_old_term args)
    | LogicOld.Atom.App (LogicOld.Predicate.Fixpoint _, _, _) ->
        failwith "conversion of fixpoint is not implemented yet"

  and of_old_formula phi =
    match Domain.DLS.get term_conversion_scope with
    | None -> of_old_formula_node phi
    | Some tbls -> (
        match OldFmlPhysTbl.find_opt tbls.of_old_fml_tbl phi with
        | Some t -> t
        | None ->
            let t = of_old_formula_node phi in
            OldFmlPhysTbl.add tbls.of_old_fml_tbl phi t;
            t)

  and of_old_formula_node = function
    | LogicOld.Formula.Atom (atom, _) -> of_old_atom atom
    | LogicOld.Formula.UnaryOp (unop, phi, _) ->
        mk_app (of_unop unop) (of_old_formula phi)
    | LogicOld.Formula.BinaryOp (binop, p1, p2, _) ->
        mk_app (mk_app (of_binop binop) (of_old_formula p1)) (of_old_formula p2)
    | LogicOld.Formula.Bind (bind, args, phi, _) ->
        let bind =
          match bind with
          | LogicOld.Formula.Forall -> Forall
          | LogicOld.Formula.Exists -> Exists
          | LogicOld.Formula.Random _ -> failwith "unimplemented"
        in
        List.fold_right ~init:(of_old_formula phi) args ~f:(fun (tvar, sort) ->
            mk_bind bind tvar (of_old_sort sort))
    | LogicOld.Formula.LetRec _ ->
        failwith "conversion of letrec is not implemented yet"
    | LogicOld.Formula.LetFormula (var, sort, def, body, _) ->
        mk_let var (of_old_sort sort) (of_old_term def) (of_old_formula body)

  let of_old (uni_senv, phi) =
    with_shared_datatype_conversion (fun () ->
        (Map.Poly.map ~f:of_old_sort uni_senv, of_old_formula phi))

  (* The same per-call table as in [of_old_sort_in], in the other direction:
     each shared datatype value is converted once per top-level call. *)
  let rec to_old_cont_in tbl = function
    | Sort.EVar x -> LogicOld.Sort.EVar x
    | Sort.Pure -> LogicOld.Sort.Pure
    | Sort.Eff (c1, c2) ->
        LogicOld.Sort.mk_cont_eff (to_old_triple_in tbl c1)
          (to_old_triple_in tbl c2)
    | _ -> failwith "to_old_cont"

  and to_old_sort_in tbl = function
    | Sort.SVar svar -> LogicOld.Sort.SVar svar
    | Sort.SArrow (s, c) ->
        LogicOld.Sort.SArrow (to_old_sort_in tbl s, to_old_triple_in tbl c)
    | SBool -> LogicOld.T_bool.SBool
    | SInt -> LogicOld.T_int.SInt
    | SReal -> LogicOld.T_real.SReal
    | SBV size -> LogicOld.T_bv.SBV size
    | SString -> LogicOld.T_string.SString
    | STrace fin -> LogicOld.T_trace.STrace fin
    | SRegEx -> LogicOld.T_regex.SRegEx
    | SArray (s1, s2) ->
        LogicOld.T_array.SArray (to_old_sort_in tbl s1, to_old_sort_in tbl s2)
    | SSeq se -> LogicOld.T_seq.SSeq (to_old_sort_in tbl se)
    | STuple sorts ->
        LogicOld.T_tuple.STuple (List.map sorts ~f:(to_old_sort_in tbl))
    | SDT dt -> (
        let tbl =
          match (tbl, Domain.DLS.get dt_conversion_scope) with
          | Some tbl, _ -> tbl
          | None, Some scope -> scope.to_old_tbl
          | None, None -> NewDtPhysTbl.create 16
        in
        match NewDtPhysTbl.find_opt tbl dt with
        | Some dt' -> LogicOld.T_dt.SDT dt'
        | None ->
            let dt' = Datatype.to_old (to_old_sort_in (Some tbl)) dt in
            NewDtPhysTbl.add tbl dt dt';
            LogicOld.T_dt.SDT dt')
    | SUS (name, args) ->
        LogicOld.T_dt.SUS (name, List.map args ~f:(to_old_sort_in tbl))
    | SRef sort -> LogicOld.T_ref.SRef (to_old_sort_in tbl sort)
    | _ -> failwith "unknown sort"

  and to_old_opsig_in tbl = function
    | Sort.OpSig (opmap, rv) ->
        LogicOld.Sort.OpSig (ALMap.map opmap ~f:(to_old_sort_in tbl), rv)
    | _ -> failwith "of_old_opsig"

  and to_old_triple_in tbl (c : Sort.c) : LogicOld.Sort.c =
    {
      op_sig = to_old_opsig_in tbl c.op_sig;
      val_type = to_old_sort_in tbl c.val_type;
      cont_eff = to_old_cont_in tbl c.cont_eff;
    }

  let to_old_sort = to_old_sort_in None

  let to_old_sort_bind (x, s) = (x, to_old_sort s)

  let to_old_unop = function
    | Not -> LogicOld.Formula.Not |> Option.some
    | _ -> None

  let to_old_binop = function
    | And -> LogicOld.Formula.And |> Option.some
    | Or -> LogicOld.Formula.Or |> Option.some
    | Imply -> LogicOld.Formula.Imply |> Option.some
    | Iff -> LogicOld.Formula.Iff |> Option.some
    | Xor -> LogicOld.Formula.Xor |> Option.some
    | _ -> None

  let to_old_fun_sym = function
    | IfThenElse -> LogicOld.T_bool.IfThenElse |> Option.some
    | Case n -> LogicOld.T_int.Case n |> Option.some
    | Int n -> LogicOld.T_int.Int n |> Option.some
    | Neg -> LogicOld.T_int.Neg |> Option.some
    | Abs -> LogicOld.T_int.Abs |> Option.some
    | Add -> LogicOld.T_int.Add |> Option.some
    | Sub -> LogicOld.T_int.Sub |> Option.some
    | Mul -> LogicOld.T_int.Mul |> Option.some
    | Div m -> LogicOld.T_int.Div m |> Option.some
    | Rem m -> LogicOld.T_int.Rem m |> Option.some
    | Power -> LogicOld.T_int.Power |> Option.some
    | Real r -> LogicOld.T_real.Real r |> Option.some
    | RNeg -> LogicOld.T_real.RNeg |> Option.some
    | RAbs -> LogicOld.T_real.RAbs |> Option.some
    | RAdd -> LogicOld.T_real.RAdd |> Option.some
    | RSub -> LogicOld.T_real.RSub |> Option.some
    | RMul -> LogicOld.T_real.RMul |> Option.some
    | RDiv -> LogicOld.T_real.RDiv |> Option.some
    | RPower -> LogicOld.T_real.RPower |> Option.some
    | BVNum (size, n) -> LogicOld.T_bv.BVNum (size, n) |> Option.some
    | BVNot size -> LogicOld.T_bv.BVNot size |> Option.some
    | BVAnd size -> LogicOld.T_bv.BVAnd size |> Option.some
    | BVOr size -> LogicOld.T_bv.BVOr size |> Option.some
    | BVXor size -> LogicOld.T_bv.BVXor size |> Option.some
    | BVNand size -> LogicOld.T_bv.BVNand size |> Option.some
    | BVNor size -> LogicOld.T_bv.BVNor size |> Option.some
    | BVXnor size -> LogicOld.T_bv.BVXnor size |> Option.some
    | BVNeg size -> LogicOld.T_bv.BVNeg size |> Option.some
    | BVAdd size -> LogicOld.T_bv.BVAdd size |> Option.some
    | BVSub size -> LogicOld.T_bv.BVSub size |> Option.some
    | BVMul size -> LogicOld.T_bv.BVMul size |> Option.some
    | BVDiv (size, signed) -> LogicOld.T_bv.BVDiv (size, signed) |> Option.some
    | BVRem (size, signed) -> LogicOld.T_bv.BVRem (size, signed) |> Option.some
    | BVSMod size -> LogicOld.T_bv.BVSMod size |> Option.some
    | BVSHL size -> LogicOld.T_bv.BVSHL size |> Option.some
    | BVLSHR size -> LogicOld.T_bv.BVLSHR size |> Option.some
    | BVASHR size -> LogicOld.T_bv.BVASHR size |> Option.some
    | BVEXTRACT (size, h, l) ->
        LogicOld.T_bv.BVEXTRACT (size, h, l) |> Option.some
    | BVSEXT (size, ext) -> LogicOld.T_bv.BVSEXT (size, ext) |> Option.some
    | BVZEXT (size, ext) -> LogicOld.T_bv.BVZEXT (size, ext) |> Option.some
    | BVCONCAT (size1, size2) ->
        LogicOld.T_bv.BVCONCAT (size1, size2) |> Option.some
    | IntToReal -> LogicOld.T_irb.IntToReal |> Option.some
    | RealToInt -> LogicOld.T_irb.RealToInt |> Option.some
    | IntToBV size -> LogicOld.T_irb.IntToBV size |> Option.some
    | BVToInt (size, signed) ->
        LogicOld.T_irb.BVToInt (size, signed) |> Option.some
    | StrConst str -> LogicOld.T_string.StrConst str |> Option.some
    | TrEpsilon -> LogicOld.T_trace.TrEpsilon |> Option.some
    | TrSymbol ev -> LogicOld.T_trace.TrSymbol ev |> Option.some
    | TrConcat fin -> LogicOld.T_trace.TrConcat fin |> Option.some
    | TrLeftQuotient fin -> LogicOld.T_trace.TrLeftQuotient fin |> Option.some
    | TrRightQuotient fin -> LogicOld.T_trace.TrRightQuotient fin |> Option.some
    | RegEmpty -> LogicOld.T_regex.RegEmpty |> Option.some
    | RegFull -> LogicOld.T_regex.RegFull |> Option.some
    | RegAllChar -> LogicOld.T_regex.RegAllChar |> Option.some
    | RegEpsilon -> LogicOld.T_regex.RegEpsilon |> Option.some
    | RegStr -> LogicOld.T_regex.RegStr |> Option.some
    | RegComplement -> LogicOld.T_regex.RegComplement |> Option.some
    | RegStar -> LogicOld.T_regex.RegStar |> Option.some
    | RegPlus -> LogicOld.T_regex.RegPlus |> Option.some
    | RegOpt -> LogicOld.T_regex.RegOpt |> Option.some
    | RegConcat -> LogicOld.T_regex.RegConcat |> Option.some
    | RegUnion -> LogicOld.T_regex.RegUnion |> Option.some
    | RegInter -> LogicOld.T_regex.RegInter |> Option.some
    | AConst (s1, s2) ->
        LogicOld.T_array.AConst (to_old_sort s1, to_old_sort s2) |> Option.some
    | AStore (s1, s2) ->
        LogicOld.T_array.AStore (to_old_sort s1, to_old_sort s2) |> Option.some
    | ASelect (s1, s2) ->
        LogicOld.T_array.ASelect (to_old_sort s1, to_old_sort s2) |> Option.some
    | SqEmpty se -> LogicOld.T_seq.SqEmpty (to_old_sort se) |> Option.some
    | SqUnit se -> LogicOld.T_seq.SqUnit (to_old_sort se) |> Option.some
    | SqConcat se -> LogicOld.T_seq.SqConcat (to_old_sort se) |> Option.some
    | SqLen se -> LogicOld.T_seq.SqLen (to_old_sort se) |> Option.some
    | SqNth se -> LogicOld.T_seq.SqNth (to_old_sort se) |> Option.some
    | SqExtract se -> LogicOld.T_seq.SqExtract (to_old_sort se) |> Option.some
    | SqStore se -> LogicOld.T_seq.SqStore (to_old_sort se) |> Option.some
    | TupleCons sorts ->
        LogicOld.T_tuple.TupleCons (List.map sorts ~f:to_old_sort)
        |> Option.some
    | TupleSel (sorts, i) ->
        LogicOld.T_tuple.TupleSel (List.map sorts ~f:to_old_sort, i)
        |> Option.some
    | DTCons (name, sorts, dt) ->
        LogicOld.T_dt.DTCons
          (name, List.map sorts ~f:to_old_sort, Datatype.to_old to_old_sort dt)
        |> Option.some
    | DTSel (name, dt, sort) ->
        LogicOld.T_dt.DTSel
          (name, Datatype.to_old to_old_sort dt, to_old_sort sort)
        |> Option.some
    | Ref sort -> LogicOld.T_ref.Ref (to_old_sort sort) |> Option.some
    | Deref sort -> LogicOld.T_ref.Deref (to_old_sort sort) |> Option.some
    | Update sort -> LogicOld.T_ref.Update (to_old_sort sort) |> Option.some
    | _ -> None

  let to_old_pred_sym = function
    | Eq -> LogicOld.T_bool.Eq |> Option.some
    | Neq -> LogicOld.T_bool.Neq |> Option.some
    | Leq -> LogicOld.T_int.Leq |> Option.some
    | Geq -> LogicOld.T_int.Geq |> Option.some
    | Lt -> LogicOld.T_int.Lt |> Option.some
    | Gt -> LogicOld.T_int.Gt |> Option.some
    | PDiv -> LogicOld.T_int.PDiv |> Option.some
    | NotPDiv -> LogicOld.T_int.NotPDiv |> Option.some
    | RLeq -> LogicOld.T_real.RLeq |> Option.some
    | RGeq -> LogicOld.T_real.RGeq |> Option.some
    | RLt -> LogicOld.T_real.RLt |> Option.some
    | RGt -> LogicOld.T_real.RGt |> Option.some
    | BVLeq (size, signed) -> LogicOld.T_bv.BVLeq (size, signed) |> Option.some
    | BVGeq (size, signed) -> LogicOld.T_bv.BVGeq (size, signed) |> Option.some
    | BVLt (size, signed) -> LogicOld.T_bv.BVLt (size, signed) |> Option.some
    | BVGt (size, signed) -> LogicOld.T_bv.BVGt (size, signed) |> Option.some
    | IsInt -> LogicOld.T_irb.IsInt |> Option.some
    | IsPrefix fin -> LogicOld.T_trace.IsPrefix fin |> Option.some
    | NotIsPrefix fin -> LogicOld.T_trace.NotIsPrefix fin |> Option.some
    | TrInRegExp (fin, regexp) ->
        LogicOld.T_trace.TrInRegExp (fin, regexp) |> Option.some
    | NotTrInRegExp (fin, regexp) ->
        LogicOld.T_trace.NotTrInRegExp (fin, regexp) |> Option.some
    | StrInRegExp -> LogicOld.T_regex.StrInRegExp |> Option.some
    | NotStrInRegExp -> LogicOld.T_regex.NotStrInRegExp |> Option.some
    | IsTuple sorts ->
        LogicOld.T_tuple.IsTuple (List.map ~f:to_old_sort sorts) |> Option.some
    | NotIsTuple sorts ->
        LogicOld.T_tuple.NotIsTuple (List.map ~f:to_old_sort sorts)
        |> Option.some
    | IsCons (name, dt) ->
        LogicOld.T_dt.IsCons (name, Datatype.to_old to_old_sort dt)
        |> Option.some
    | NotIsCons (name, dt) ->
        LogicOld.T_dt.NotIsCons (name, Datatype.to_old to_old_sort dt)
        |> Option.some
    | _ -> None

  let fenv_sorts_of fenv =
    Map.Poly.map fenv ~f:(fun (params, sret, _, _, _) ->
        of_old_sort (LogicOld.Sort.mk_fun (List.map params ~f:snd @ [ sret ])))

  (* The sort environment the conversion asks [sort_of] in when it must
     know a subterm's sort to choose an encoding (an [ite] or an equality at
     [Bool]).  Besides the two environments the caller passes, it holds the
     functions defined by [define-fun-rec] (the process-global function
     environment), which a term applies as variables: without them [sort_of]
     fails with "<f> not found" on any [ite] whose branch applies such a
     function, although the variable lookup of [to_old_term] itself already
     falls back to that environment.  A name bound by the caller shadows a
     defined function.  This is the definition; [sort_senv_of] below gives
     the same map, binding for binding, and raises where this raises. *)
  let sort_senv_of_rebuilt exi_senv uni_senv =
    Map.Poly.fold (LogicOld.get_fenv ())
      ~init:(Map.force_merge exi_senv uni_senv)
      ~f:(fun ~key ~data:(params, sret, _, _, _) senv ->
        if Map.Poly.mem senv key then senv
        else
          Map.Poly.set senv ~key
            ~data:
              (of_old_sort
                 (LogicOld.Sort.mk_fun (List.map params ~f:snd @ [ sret ]))))

  (* [exi_senv] with the defined functions' sorts it does not shadow, for the
     unknowns' environment and the function environment last seen on this
     domain, both compared physically (immutable maps, replaced as a whole when
     they change).  [None] when some defined function's sort does not convert,
     in which case [sort_senv_of] falls back to the definition and raises
     where it raises. *)
  let base_senv_cache :
      (sort_env_map * LogicOld.FunEnv.t * sort_env_map option) option
      Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  (* the defined functions' sorts alone, for the function environment last
     seen on this domain: a caller that passes a new unknowns' environment
     each time still converts them once *)
  let fenv_sorts_cache :
      (LogicOld.FunEnv.t * sort_env_map option) option Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  let fenv_sorts fenv =
    match Domain.DLS.get fenv_sorts_cache with
    | Some (fenv', sorts) when phys_equal fenv fenv' -> sorts
    | _ ->
        let sorts =
          try Some (fenv_sorts_of fenv)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        in
        Domain.DLS.set fenv_sorts_cache (Some (fenv, sorts));
        sorts

  let base_senv exi_senv fenv =
    match Domain.DLS.get base_senv_cache with
    | Some (exi', fenv', base)
      when phys_equal exi_senv exi' && phys_equal fenv fenv' ->
        base
    | _ ->
        let base =
          Option.map (fenv_sorts fenv) ~f:(fun sorts ->
              Map.Poly.merge_skewed exi_senv sorts
                ~combine:(fun ~key:_ bound _ -> bound))
        in
        Domain.DLS.set base_senv_cache (Some (exi_senv, fenv, base));
        base

  (* [sort_senv_of_rebuilt] without rebuilding: the environment is asked for at
     each [ite] and each [Bool] equality, and converting every defined
     function's sort and merging the unknowns' environment on each request was
     most of the conversion's time on an input with hundreds of definitions
     and unknowns.  The ordinary variables are laid over the cached base one by
     one: a variable bound by both environments with different sorts raises
     [Failure "force_merge"] as [Map.force_merge] does, one bound by the
     unknowns' environment with the same sort changes nothing, and any other
     shadows a defined function as in the definition. *)
  let sort_senv_of_uncached exi_senv uni_senv =
    let fenv = LogicOld.get_fenv () in
    match base_senv exi_senv fenv with
    | None -> sort_senv_of_rebuilt exi_senv uni_senv
    | Some base ->
        Map.Poly.fold uni_senv ~init:base ~f:(fun ~key ~data senv ->
            match Map.Poly.find exi_senv key with
            | Some data' when Stdlib.(data' = data) -> senv
            | Some _ -> failwith "force_merge"
            | None -> Map.Poly.set senv ~key ~data)

  (* The last answer of [sort_senv_of_uncached], kept per domain with the three
     maps it was computed from, physically.  The conversion asks the
     environment at every [ite] and every [Bool] equality of a clause, and
     passes the same ordinary variables' map down to every node outside a
     [let] or an array [lambda], so laying those variables over the base again
     at each node was most of the conversion's time on a clause with hundreds
     of variables; with the last answer kept it is laid once per clause and
     per binder.  The answer is a function of the three maps, so a physically
     equal triple has the same answer.  A call that raises leaves the record
     as it was. *)
  let sort_senv_last :
      (sort_env_map * sort_env_map * LogicOld.FunEnv.t * sort_env_map) option
      Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  let sort_senv_of exi_senv uni_senv =
    let fenv = LogicOld.get_fenv () in
    match Domain.DLS.get sort_senv_last with
    | Some (exi', uni', fenv', senv)
      when phys_equal exi_senv exi' && phys_equal uni_senv uni'
           && phys_equal fenv fenv' ->
        senv
    | _ ->
        let senv = sort_senv_of_uncached exi_senv uni_senv in
        Domain.DLS.set sort_senv_last (Some (exi_senv, uni_senv, fenv, senv));
        senv

  let rec to_old_term exi_senv uni_senv term args =
    match (term, args) with
    | Var (tvar, _), args ->
        let sort =
          match Map.Poly.find exi_senv tvar with
          | Some sort -> to_old_sort sort
          | None -> (
              match Map.Poly.find uni_senv tvar with
              | Some sort -> to_old_sort sort
              | None -> (
                  let dum_senv = LogicOld.get_dummy_term_senv () in
                  match List.Assoc.find dum_senv ~equal:Stdlib.( = ) tvar with
                  | Some sort -> sort
                  | None -> (
                      let fenv = LogicOld.get_fenv () in
                      match Map.Poly.find fenv tvar with
                      | Some (params, sret, _, _, _) ->
                          LogicOld.Sort.mk_fun
                            (List.map params ~f:snd @ [ sret ])
                      | None ->
                          (* the four environments this lookup searched, so that the
                             failure below can be diagnosed -- on STDERR, because
                             stdout carries the verdict and a caller reading it
                             for one used to get these four lines instead *)
                          if Atomic.get print_unbound_envs then (
                          prerr_endline @@ sprintf "exi_senv: %s"
                          @@ str_of_sort_env_map str_of_sort exi_senv;
                          prerr_endline @@ sprintf "uni_senv: %s"
                          @@ str_of_sort_env_map str_of_sort uni_senv;
                          prerr_endline @@ sprintf "dum_senv: %s"
                          @@ LogicOld.str_of_sort_env_list
                               LogicOld.Term.str_of_sort dum_senv;
                          prerr_endline @@ sprintf "fenv: %s"
                          @@ LogicOld.FunEnv.str_of fenv);
                          failwith
                          @@ sprintf "[to_old_term] %s is not bound"
                          @@ Ident.name_of_tvar tvar)))
        in
        if List.is_empty args then LogicOld.Term.mk_var tvar sort
        else
          let args' = List.map args ~f:(to_old_trm exi_senv uni_senv) in
          let sargs, sret = LogicOld.Sort.args_ret_of sort in
          if Map.Poly.mem exi_senv tvar && LogicOld.Term.is_bool_sort sret then
            LogicOld.T_bool.of_atom
            @@ LogicOld.Atom.mk_pvar_app (Ident.tvar_to_pvar tvar) sargs args'
          else LogicOld.Term.mk_fvar_app tvar sargs sret args'
    | Con (ALambda (si, se), _), [ Bin (Lambda, x, _, body, _) ] ->
        LogicOld.T_array.mk_lambda
          (x, to_old_sort si)
          (to_old_sort se)
          (to_old_trm exi_senv (Map.Poly.set uni_senv ~key:x ~data:si) body)
    | Con (sym, _), args -> (
        match to_old_fun_sym sym with
        | Some old_sym ->
            LogicOld.Term.mk_fsym_app old_sym
            @@ List.map args ~f:(to_old_trm exi_senv uni_senv)
        | None ->
            LogicOld.T_bool.of_formula
              (to_old_formula exi_senv uni_senv term args))
    | App (t1, t2, _), args -> to_old_term exi_senv uni_senv t1 (t2 :: args)
    | Bin ((Forall | Exists), _, _, _, _), [] ->
        LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv term args)
    | Bin (Lambda, _, _, _, _), [] ->
        failwith "[to_old_term] partial application not supported"
    | Bin (Lambda, tvar, _, t, _), arg :: args' ->
        to_old_term exi_senv uni_senv
          (subst (Map.Poly.singleton tvar arg) t)
          args'
    | Let (var, sort, def, body, _), args ->
        LogicOld.Term.mk_let_term var (to_old_sort sort)
          (to_old_trm exi_senv uni_senv def)
          (to_old_term exi_senv
             (Map.Poly.set uni_senv ~key:var ~data:sort)
             body args)
    | TyApp (Con (((Eq | Neq) as op), _), _, _), [ t1; t2 ] ->
        let t1' = to_old_trm exi_senv uni_senv t1 in
        let t2' = to_old_trm exi_senv uni_senv t2 in
        LogicOld.T_bool.(
          of_atom @@ (if Stdlib.(op = Eq) then mk_eq else mk_neq) t1' t2')
    | ( TyApp (Con (IfThenElse, _), (SBool | Sort.SVar _), _),
        t1 :: t2 :: t3 :: args )
      when BoolTerm.is_bool_sort
             (head_sort_of (sort_senv_of exi_senv uni_senv) t2) ->
        LogicOld.T_bool.(
          mk_if_then_else
            (of_formula (to_old_fml exi_senv uni_senv t1))
            (of_formula (to_old_formula exi_senv uni_senv t2 args))
            (of_formula (to_old_formula exi_senv uni_senv t3 args)))
    | TyApp (Con (IfThenElse, _), _, _), t1 :: t2 :: t3 :: args ->
        LogicOld.T_bool.(
          mk_if_then_else
            (of_formula (to_old_fml exi_senv uni_senv t1))
            (to_old_term exi_senv uni_senv t2 args)
            (to_old_term exi_senv uni_senv t3 args))
    | TyApp (Con (Leq, _), Sort.SVar svar, _), [ t1; t2 ] ->
        let t1' = to_old_trm exi_senv uni_senv t1 in
        let t2' = to_old_trm exi_senv uni_senv t2 in
        LogicOld.(
          T_bool.of_atom @@ Atom.mk_psym_app (T_num.NLeq svar) [ t1'; t2' ])
    | TyApp (Con (Geq, _), Sort.SVar svar, _), [ t1; t2 ] ->
        let t1' = to_old_trm exi_senv uni_senv t1 in
        let t2' = to_old_trm exi_senv uni_senv t2 in
        LogicOld.(
          T_bool.of_atom @@ Atom.mk_psym_app (T_num.NGeq svar) [ t1'; t2' ])
    | TyApp (Con (Lt, _), Sort.SVar svar, _), [ t1; t2 ] ->
        let t1' = to_old_trm exi_senv uni_senv t1 in
        let t2' = to_old_trm exi_senv uni_senv t2 in
        LogicOld.(
          T_bool.of_atom @@ Atom.mk_psym_app (T_num.NLt svar) [ t1'; t2' ])
    | TyApp (Con (Gt, _), Sort.SVar svar, _), [ t1; t2 ] ->
        let t1' = to_old_trm exi_senv uni_senv t1 in
        let t2' = to_old_trm exi_senv uni_senv t2 in
        LogicOld.(
          T_bool.of_atom @@ Atom.mk_psym_app (T_num.NGt svar) [ t1'; t2' ])
    | TyApp (Con (Case n, _), (SBool | Sort.SVar _), _), t1 :: args
      when List.length args >= 1
           && BoolTerm.is_bool_sort
                (head_sort_of (sort_senv_of exi_senv uni_senv) (List.hd_exn args))
      ->
        let args1, args2 = List.split_n args n in
        LogicOld.(
          T_int.mk_case n (to_old_trm exi_senv uni_senv t1)
          @@ List.map args1 ~f:(fun t ->
              T_bool.of_formula (to_old_formula exi_senv uni_senv t args2)))
    | TyApp (Con (Case n, _), _, _), t1 :: args ->
        let args1, args2 = List.split_n args n in
        LogicOld.(
          T_int.mk_case n (to_old_trm exi_senv uni_senv t1)
          @@ List.map args1 ~f:(fun t -> to_old_term exi_senv uni_senv t args2))
    (*| TyApp (t, _sort, _), args (* ToDo: use [sort] *) ->
      to_old_term exi_senv uni_senv t args*)
    | TyLam _, _ -> failwith "[to_old_term] tylam not implemented"
    | _ ->
        failwith
        @@ sprintf "[to_old_term] unknown term: %s(%s)" (str_of term)
             (String.concat_map_list ~sep:"," args ~f:str_of)

  and to_old_trm exi_senv uni_senv term =
    match (term, Domain.DLS.get term_conversion_scope) with
    | App _, Some tbls when Atomic.get share_term_conversion_terms -> (
        let entries =
          Option.value ~default:[]
            (TermPhysTbl.find_opt tbls.to_old_term_tbl term)
        in
        match
          List.find entries ~f:(fun e ->
              to_old_reusable_in tbls exi_senv uni_senv term e.tentry_exi
                e.tentry_uni)
        with
        | Some e -> e.tentry_img
        | None ->
            let stamp = Ident.fresh_stamp () in
            let img = to_old_term exi_senv uni_senv term [] in
            if Ident.fresh_stamp () = stamp then
              TermPhysTbl.replace tbls.to_old_term_tbl term
                ({ tentry_exi = exi_senv; tentry_uni = uni_senv; tentry_img = img }
                :: List.take entries (to_old_entries_per_term - 1));
            img)
    | _ -> to_old_term exi_senv uni_senv term []

  and to_old_atom exi_senv uni_senv term args =
    match (term, args) with
    | Var ((Ident.Tvar name as tvar), _), args -> (
        let args' = List.map args ~f:(to_old_trm exi_senv uni_senv) in
        match Map.Poly.find exi_senv tvar with
        | Some sort ->
            let sargs, sret = LogicOld.Sort.args_ret_of @@ to_old_sort sort in
            assert (LogicOld.Term.is_bool_sort sret);
            LogicOld.Atom.mk_pvar_app (Ident.Pvar name) sargs args'
        | None -> (
            match Map.Poly.find uni_senv tvar with
            | Some sort ->
                let sargs, sret =
                  LogicOld.Sort.args_ret_of @@ to_old_sort sort
                in
                assert (LogicOld.Term.is_bool_sort sret);
                LogicOld.Atom.of_bool_term
                @@
                if List.is_empty sargs then LogicOld.Term.mk_var tvar sret
                else if true then
                  LogicOld.Term.mk_fvar_app (*ToDo*) tvar sargs sret args'
                else
                  failwith
                  @@ sprintf "%s(%s)" (Ident.name_of_tvar tvar)
                       (String.concat_map_list ~sep:"," args ~f:str_of)
            | None -> (
                let dum_senv = LogicOld.get_dummy_term_senv () in
                match List.Assoc.find dum_senv ~equal:Stdlib.( = ) tvar with
                | Some sort ->
                    let sargs, sret = LogicOld.Sort.args_ret_of sort in
                    assert (LogicOld.Term.is_bool_sort sret);
                    LogicOld.(
                      Atom.of_bool_term
                      @@ Term.mk_fvar_app (Ident.Tvar name) sargs sret args')
                | None -> (
                    let fenv = LogicOld.get_fenv () in
                    match Map.Poly.find fenv tvar with
                    | Some (params, sret, _, _, _) ->
                        assert (LogicOld.Term.is_bool_sort sret);
                        let sargs = List.map params ~f:snd in
                        LogicOld.(
                          Atom.of_bool_term
                          @@ Term.mk_fvar_app tvar sargs sret args')
                    | None ->
                        (* on STDERR: stdout carries the verdict, and a caller
                           reading it for one used to get these four lines *)
                        if Atomic.get print_unbound_envs then (
                        prerr_endline @@ sprintf "exi_senv: %s"
                        @@ str_of_sort_env_map str_of_sort exi_senv;
                        prerr_endline @@ sprintf "uni_senv: %s"
                        @@ str_of_sort_env_map str_of_sort uni_senv;
                        prerr_endline @@ sprintf "dum_senv: %s"
                        @@ LogicOld.str_of_sort_env_list
                             LogicOld.Term.str_of_sort dum_senv;
                        prerr_endline @@ sprintf "fenv: %s"
                        @@ LogicOld.FunEnv.str_of fenv);
                        failwith (sprintf "[to_old_atom] %s is not bound" name))
                )))
    | Con (True, _), [] -> LogicOld.Atom.mk_true ()
    | Con (False, _), [] -> LogicOld.Atom.mk_false ()
    | Con (ASelect _, _), args ->
        LogicOld.Atom.of_bool_term @@ to_old_term exi_senv uni_senv term args
    | Con ((SqNth _ | TupleSel _ | Deref _), _), args ->
        (* a read of a sequence, tuple or reference whose element is Bool, standing
           as an atom: a Bool-valued function application like [ASelect] above, not
           a predicate symbol *)
        LogicOld.Atom.of_bool_term @@ to_old_term exi_senv uni_senv term args
    | Con (ALambda _, _), args ->
        (* delegate to [to_old_term], which binds the lambda variable before
           descending; reaching the body any other way would visit the [Bin
           (Lambda, ...)] unapplied *)
        LogicOld.Atom.of_bool_term @@ to_old_term exi_senv uni_senv term args
    | Con (DTSel (name, dt, _), _), [ arg ] ->
        LogicOld.Atom.of_bool_term
        @@ LogicOld.T_dt.mk_sel (Datatype.to_old to_old_sort dt) name
        @@ to_old_trm exi_senv uni_senv arg
    | (Con (sym, _) as term), args ->
        let pred =
          match to_old_pred_sym sym with
          | Some pred_sym -> LogicOld.Predicate.mk_psym pred_sym
          | None ->
              failwith
                (sprintf "[to_old_atom] unknown pred. symbol: %s" @@ str_of term)
        in
        LogicOld.Atom.mk_app pred
        @@ List.map args ~f:(to_old_trm exi_senv uni_senv)
    | App (t1, t2, _), args -> to_old_atom exi_senv uni_senv t1 (t2 :: args)
    | Bin (Lambda, _, _, _, _), [] ->
        failwith "[to_old_atom] partial application not supported"
    | Bin (Lambda, tvar, _, t, _), arg :: args' ->
        to_old_atom exi_senv uni_senv
          (subst (Map.Poly.singleton tvar arg) t)
          args'
    | Let (var, sort, def, body, _), args ->
        LogicOld.Atom.insert_let_pvar_app var (to_old_sort sort)
          (to_old_trm exi_senv uni_senv def)
          LogicOld.Dummy
        (* ToDo *)
        @@ to_old_atom exi_senv
             (Map.Poly.set uni_senv ~key:var ~data:sort)
             body args
    | TyApp (Con (((Eq | Neq) as op), _), _, _), [ t1; t2 ] ->
        LogicOld.(if Stdlib.(op = Eq) then T_bool.mk_eq else T_bool.mk_neq)
          (to_old_trm exi_senv uni_senv t1)
          (to_old_trm exi_senv uni_senv t2)
    | ( TyApp (Con (IfThenElse, _), (SBool | Sort.SVar _), _),
        t1 :: t2 :: t3 :: args )
      when BoolTerm.is_bool_sort
             (head_sort_of (sort_senv_of exi_senv uni_senv) t2) ->
        LogicOld.Atom.of_bool_term
        @@ LogicOld.T_bool.(
             mk_if_then_else
               (of_formula (to_old_fml exi_senv uni_senv t1))
               (of_formula (to_old_formula exi_senv uni_senv t2 args))
               (of_formula (to_old_formula exi_senv uni_senv t3 args)))
    (*LogicOld.Formula.mk_or
      (LogicOld.Formula.mk_and t1' t2')
      (LogicOld.Formula.mk_and (LogicOld.Formula.mk_neg t1') t3')*)
    | TyApp (Con (Case n, _), (SBool | Sort.SVar _), _), t1 :: args
      when List.length args >= 1
           && BoolTerm.is_bool_sort
                (head_sort_of (sort_senv_of exi_senv uni_senv) (List.hd_exn args))
      ->
        let args1, args2 = List.split_n args n in
        LogicOld.(
          Atom.of_bool_term
          @@ T_int.mk_case n (to_old_trm exi_senv uni_senv t1)
          @@ List.map args1 ~f:(fun t ->
              T_bool.of_formula (to_old_formula exi_senv uni_senv t args2)))
    (* a numeric comparison whose sort is still a variable (type inference
       did not pin it) goes back as the polymorphic [T_num] symbol, as the
       term direction ([to_old_term]) already does; the generic arm below
       drops the sort and [to_old_pred_sym] then makes it [T_int.Leq], a
       silent default to Int.  Both entry points, [to_old_atm] and
       [to_old_fml], reach this arm, so they agree.  No input reaches it
       today: the frontends declare every sort. *)
    | TyApp (Con (((Leq | Geq | Lt | Gt) as cmp), _), Sort.SVar svar, _), args
      when List.length args = 2 ->
        let psym =
          match cmp with
          | Leq -> LogicOld.T_num.NLeq svar
          | Geq -> LogicOld.T_num.NGeq svar
          | Lt -> LogicOld.T_num.NLt svar
          | _ -> LogicOld.T_num.NGt svar
        in
        LogicOld.Atom.mk_psym_app psym
          (List.map args ~f:(to_old_trm exi_senv uni_senv))
    | TyApp (t, _sort, _), args (* ToDo: use [sort] *) ->
        to_old_atom exi_senv uni_senv t args
    | _ ->
        failwith
        @@ sprintf "[to_old_atom] unknown term: %s(%s)" (str_of term)
             (String.concat_map_list ~sep:"," args ~f:str_of)

  and to_old_atm exi_senv uni_senv term = to_old_atom exi_senv uni_senv term []

  and to_old_formula exi_senv uni_senv term args =
    let rec aux uni_senv term args ~next =
      match (args, term, Domain.DLS.get term_conversion_scope) with
      | [], App _, Some tbls ->
          let entries =
            Option.value ~default:[]
              (TermPhysTbl.find_opt tbls.to_old_fml_tbl term)
          in
          let img =
            match
              List.find entries ~f:(to_old_reusable tbls exi_senv uni_senv term)
            with
            | Some e -> e.entry_img
            | None ->
                let stamp = Ident.fresh_stamp () in
                let img = aux_node uni_senv term [] ~next:Fn.id in
                if
                  (not (Atomic.get share_term_conversion_terms))
                  || Ident.fresh_stamp () = stamp
                then
                  TermPhysTbl.replace tbls.to_old_fml_tbl term
                    ({ entry_exi = exi_senv; entry_uni = uni_senv; entry_img = img }
                    :: List.take entries (to_old_entries_per_term - 1));
                img
          in
          next img
      | _ -> aux_node uni_senv term args ~next
    and aux_node uni_senv term args ~next =
      match term with
      | Var _ ->
          next @@ LogicOld.Formula.mk_atom
          @@ to_old_atom exi_senv uni_senv term args
      | Con (sym, _) -> (
          match to_old_unop sym with
          | Some unop_sym -> (
              match args with
              | [ t ] ->
                  aux uni_senv t []
                    ~next:(LogicOld.Formula.mk_unop unop_sym >> next)
              | _ -> assert false)
          | None -> (
              match to_old_binop sym with
              | Some binop_sym -> (
                  match args with
                  | [ t1; t2 ] ->
                      aux uni_senv t1 [] ~next:(fun t1' ->
                          aux uni_senv t2 [] ~next:(fun t2' ->
                              next
                              @@ LogicOld.Formula.mk_binop binop_sym t1' t2'))
                  | _ ->
                      failwith (String.concat_map_list ~sep:"\n" ~f:str_of args)
                  )
              | None ->
                  next @@ LogicOld.Formula.mk_atom
                  @@ to_old_atom exi_senv uni_senv term args))
      | App (t1, t2, _) -> aux uni_senv t1 (t2 :: args) ~next
      | Bin (Forall, tvar, s, t, _) -> (
          match args with
          | [] ->
              aux
                (Map.Poly.set uni_senv ~key:tvar ~data:s)
                t []
                ~next:
                  (LogicOld.Formula.mk_forall [ (tvar, to_old_sort s) ] >> next)
          | _ -> assert false)
      | Bin (Exists, tvar, s, t, _) -> (
          match args with
          | [] ->
              aux
                (Map.Poly.set uni_senv ~key:tvar ~data:s)
                t []
                ~next:
                  (LogicOld.Formula.mk_exists [ (tvar, to_old_sort s) ] >> next)
          | _ -> assert false)
      | Bin (Lambda, tvar, _, t, _) -> (
          match args with
          | [] -> assert false
          | arg :: args' ->
              aux uni_senv (subst (Map.Poly.singleton tvar arg) t) args' ~next)
      | TyApp
          (Con ((Eq | Neq | IfThenElse | Case _), _), (SBool | Sort.SVar _), _)
        ->
          next @@ LogicOld.Formula.mk_atom
          @@ to_old_atom exi_senv uni_senv term args
      | TyApp (Con (IfThenElse, _), sort, _) -> failwith @@ str_of_sort sort
      | TyApp (Con (Case _, _), sort, _) -> failwith @@ str_of_sort sort
      (* a numeric comparison over a sort variable is an atom; [to_old_atom]
         keeps its sort, which the generic arm below would drop *)
      | TyApp (Con ((Leq | Geq | Lt | Gt), _), Sort.SVar _, _)
        when List.length args = 2 ->
          next @@ LogicOld.Formula.mk_atom
          @@ to_old_atom exi_senv uni_senv term args
      | TyApp (term, _sort, _) (* ToDo: use [sort] *) ->
          aux uni_senv term args ~next
      | Let (var, sort, def, body, _) ->
          let def = to_old_trm exi_senv uni_senv def in
          aux
            (Map.Poly.set uni_senv ~key:var ~data:sort)
            body args
            ~next:
              (LogicOld.Formula.mk_let_formula var (to_old_sort sort) def
              >> next)
      | _ ->
          failwith
          @@ sprintf "[to_old_formula] unknown term: %s(%s)" (str_of term)
               (String.concat_map_list ~sep:"," args ~f:str_of)
    in
    aux uni_senv term args ~next:Fn.id

  and to_old_fml exi_senv uni_senv term =
    with_shared_datatype_conversion (fun () ->
        to_old_formula exi_senv uni_senv term [])

  let to_old_subst exi_senv uni_senv =
    Map.Poly.map ~f:(to_old_trm exi_senv uni_senv)

  (** Construction *)

  let rec mk_dummy = function
    | Sort.SVar (Ident.Svar name) as sort ->
        let name =
          "dummy_" ^ name
          (*ToDo*)
        in
        LogicOld.add_dummy_term (Ident.Tvar name) @@ to_old_sort sort;
        mk_var (Ident.Tvar name)
    | Sort.SArrow _ as sort ->
        let name =
          sprintf "dummy_arrow(%s)"
            (LogicOld.Term.str_of_sort @@ to_old_sort sort)
        in
        LogicOld.add_dummy_term (Ident.Tvar name) @@ to_old_sort sort;
        mk_var (Ident.Tvar name)
    | SBool -> BoolTerm.mk_bool false
    | SInt -> IntTerm.zero ()
    | SReal -> RealTerm.rzero ()
    | SBV size -> BVTerm.mk_bvnum ~size Z.zero
    | SString -> mk_con @@ StrConst ""
    | STrace true -> mk_con TrEpsilon
    | STrace false -> failwith "STrace false"
    | SRegEx -> mk_con RegEmpty
    | SArray (s1, s2) -> mk_app (mk_const_array s1 s2) (mk_dummy s2)
    | SSeq se -> mk_empty se
    | STuple sorts ->
        mk_apps (mk_tuple_cons sorts) @@ List.map sorts ~f:mk_dummy
    | (SDT _ | SUS _) as sort -> DatatypeTerm.mk_dummy mk_dummy to_old_sort sort
    | SRef sort -> mk_app (mk_ref sort) @@ mk_dummy sort
    | _ -> failwith @@ "unknown sort"

  let random_term_of bound = function
    | BoolTerm.SBool -> mk_bool @@ Random.bool ()
    | IntTerm.SInt -> mk_int @@ Z.of_int (Random.int ((2 * bound) + 1) - bound)
    | RealTerm.SReal ->
        let fb = float_of_int bound in
        mk_real @@ Q.of_float @@ Random.float_range (-.fb) fb
    | data (*ToDo*) -> mk_dummy data

  (** Models *)

  let remove_dontcare_elem ((x, s), v) =
    match v with None -> (x, mk_dummy s) | Some term -> (x, term)

  let remove_dontcare = List.map ~f:remove_dontcare_elem

  (** Printing *)

  let str_of_formula exi_senv uni_senv term =
    LogicOld.Formula.str_of @@ Evaluator.simplify
    @@ to_old_fml exi_senv uni_senv term

  let str_of_term exi_senv uni_senv term =
    LogicOld.Term.str_of @@ Evaluator.simplify_term
    @@ to_old_trm exi_senv uni_senv term

  (** Transformation *)

  let simplify_formula exi_senv uni_senv t =
    try
      let param_senv, phi = let_lam t in
      let uni_senv =
        Map.force_merge uni_senv (Map.Poly.of_alist_exn param_senv)
      in
      to_old_fml exi_senv uni_senv phi
      |> Evaluator.simplify |> of_old_formula |> mk_lambda param_senv
    with e when not (Common.Timer.is_async e) -> (
      (* [let_lam] peeling is a heuristic; if the plain conversion fails as
         well, report the first failure, not the retry's *)
      try to_old_fml exi_senv uni_senv t |> Evaluator.simplify |> of_old_formula
      with exn_ when not (Common.Timer.is_async exn_) -> raise e)

  let simplify_term exi_senv uni_senv t =
    try
      let param_senv, phi = let_lam t in
      let uni_senv =
        Map.force_merge uni_senv (Map.Poly.of_alist_exn param_senv)
      in
      to_old_trm exi_senv uni_senv phi
      |> Evaluator.simplify_term |> of_old_term |> mk_lambda param_senv
    with e when not (Common.Timer.is_async e) -> (
      try
        to_old_trm exi_senv uni_senv t |> Evaluator.simplify_term |> of_old_term
      with exn_ when not (Common.Timer.is_async exn_) -> raise e)
end

let of_old_sort_env_list = List.map ~f:ExtTerm.of_old_sort_bind
let of_old_sort_env_map = Map.Poly.map ~f:ExtTerm.of_old_sort
let of_old_sort_env_set = Set.Poly.map ~f:ExtTerm.of_old_sort_bind
let to_old_sort_env_list = List.map ~f:ExtTerm.to_old_sort_bind
let to_old_sort_env_map = Map.Poly.map ~f:ExtTerm.to_old_sort
let mk_old_dummy = ExtTerm.to_old_sort >> LogicOld.Term.mk_dummy
let to_old_dummies = Map.Poly.map ~f:mk_old_dummy

(* [select_constant_cases t] is [t] with every application
   [case_n k b_0 .. b_(n-1)] whose selector [k] is an integer literal with
   [0 <= k < n] replaced by its branch [b_k] (after the same replacement inside
   it).  This is the rule the simplifier applies to such a case
   ([Evaluator.simplify_case_parts]), so the result denotes the same value as
   [t] in every model.

   Contract: the result is equal to [t] in every model; no binder is renamed
   or crossed by a substitution (a branch is a subterm already in scope), so
   nothing can be captured; a case whose selector is not an in-range literal,
   or that is applied to more arguments than its branches, is kept (its
   branches still reduced); and every subterm in which no reducible case
   occurs is returned physically, so a term without one is returned as it
   is.

   Why: a function template whose result is chosen among the hypothesis
   space's terms by a selector parameter is [case_(m+1) sel default t_1 ..
   t_m], and a candidate instantiates [sel] with a literal but keeps all [m]
   branches; with thousands of terms every application of the candidate in a
   clause carries them all through substitution, conversion and
   simplification, which reduce them to one. *)
let select_constant_cases =
  let rec go t =
    match t with
    | Var _ | Con _ -> t
    | App _ -> (
        let h, args = Term.let_apps t in
        match (h, args) with
        | TyApp (Con (IntTerm.Case n, _), _, _), sel :: branches
          when List.length branches = n -> (
            let sel' = go sel in
            match sel' with
            | Con (IntTerm.Int k, _) when Z.(leq zero k && lt k (of_int n)) ->
                go (List.nth_exn branches (Z.to_int k))
            | _ -> rebuild t h (sel :: branches) (h :: sel' :: List.map branches ~f:go))
        | _ -> rebuild t h args (go h :: List.map args ~f:go))
    | Bin (b, x, s, body, info) ->
        let body' = go body in
        if phys_equal body body' then t else Bin (b, x, s, body', info)
    | Let (x, s, t1, t2, info) ->
        let t1' = go t1 and t2' = go t2 in
        if phys_equal t1 t1' && phys_equal t2 t2' then t
        else Let (x, s, t1', t2', info)
    | TyApp (t1, s, info) ->
        let t1' = go t1 in
        if phys_equal t1 t1' then t else TyApp (t1', s, info)
    | TyLam (sv, t1, info) ->
        let t1' = go t1 in
        if phys_equal t1 t1' then t else TyLam (sv, t1', info)
  (* [t] = [h args]; [h' :: args'] are the reduced parts *)
  and rebuild t h args = function
    | h' :: args' ->
        if phys_equal h h' && List.for_all2_exn args args' ~f:phys_equal then t
        else Term.mk_apps h' args'
    | [] -> assert false
  in
  go
