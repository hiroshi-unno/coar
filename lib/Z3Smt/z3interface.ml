open Core
open Z3
open Common
open Common.Ext
open Ast
open Ast.LogicOld

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))

let validate = false
let validate_cfg = [ ("model_validate", "true"); ("well_sorted_check", "true") ]

(* let _ = Z3.set_global_param "smt.macro_finder" "true" *)
let mutex = Caml_threads.Mutex.create ()
let enable_mutex = false
let lock () = if enable_mutex then Caml_threads.Mutex.lock mutex
let unlock () = if enable_mutex then Caml_threads.Mutex.unlock mutex
let full_major () = if enable_mutex then Gc.full_major ()
let enable_solver_pool = true
type dtenv = (LogicOld.Datatype.t * Z3.Sort.sort) Set.Poly.t
type fenv = (Ident.tvar, Z3.FuncDecl.func_decl) Map.Poly.t
type instance = {
  ctx : context;
  solver : Z3.Solver.solver;
  goal : Goal.goal;
  cfg : (string * string) list;
  mutable dtenv : dtenv;
  mutable fenv : fenv;
}
let instance_pool = Hashtbl.Poly.create ()
let cache_divide_str = "__separator__"
let cache_id = Atomic.make 0
let term_cache: (context * ((Ident.tvar, Sort.t) List.Assoc.t), int * (Term.t, Expr.expr) Hashtbl.Poly.t) Hashtbl.Poly.t = Hashtbl.Poly.create ()
let bound_var_cache : (Expr.expr list) Atomic.t = Atomic.make []
let add_to_bound_var_cache e = 
  lock ();
  Atomic.set bound_var_cache @@ e::(Atomic.get bound_var_cache);
  unlock ()
let find_in_cache ~f ctx env t =
  let cid, cache =
    Hashtbl.Poly.find_or_add term_cache (ctx, env) ~default:(fun _ ->
        Atomic.incr cache_id; Atomic.get cache_id, Hashtbl.Poly.create ())
  in
  Hashtbl.Poly.find_or_add cache t ~default:(fun _ ->
      Debug.print @@ lazy ("not found: " ^ Term.str_of t);
      (* lock (); (fun ret -> unlock (); ret) @@ *)
      f cid)
let clean () =
  (* Hashtbl.Poly.clear cache; *)
  Hashtbl.Poly.clear instance_pool

let z3_solver_reset solver =
  (* lock (); (fun ret -> unlock (); ret) @@ *)
  Z3.Solver.reset solver

let z3_solver_add solver exprs =
  (* lock (); (fun ret -> unlock (); ret) @@ *)
  Z3.Solver.add solver exprs

let z3_goal_add goal exprs =
  (* lock (); (fun ret -> unlock (); ret) @@ *)
  Z3.Goal.add goal exprs

let z3_solver_get_model solver =
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.get_model solver

let z3_solver_get_unsat_core solver =
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.get_unsat_core solver

let z3_solver_assert_and_track solver e1 e2=
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.assert_and_track solver e1 e2

let debug_print_z3_input phis =
  Debug.print @@ lazy "Z3 input formulas :";
  List.iter phis ~f:(fun phi -> Debug.print @@ lazy (Formula.str_of phi))
let debug_print_z3_model model =
  Debug.print @@ lazy ("Z3 output model :" ^ LogicOld.str_of_model model)

(** decoding *)

let unint_svar_prefix = "#svar_"
let unint_is_cons_prefix = "#is_"
let unint_tuple_prefix = "#tuple"
let unint_tuple_sel_prefix = "#t_sel."
let unint_string_prefix = "#string_"
let unint_epsilon = "#epsilon"
let unint_symbol_prefix = "#symbol_"
let unint_concat_fin = "#concat_fin"
let unint_concat_inf = "#concat_inf"
let unint_is_prefix_of_fin = "#is_prefix_of_fin"
let unint_is_prefix_of_inf = "#is_prefix_of_inf"
let unint_is_in_reg_exp_fin_prefix = "#is_in_reg_exp_fin"
let unint_is_in_reg_exp_inf_prefix = "#is_in_reg_exp_inf"

let unint_string = "#string"
let unint_finseq = "#fin_seq"
let unint_infseq = "#inf_seq"
let unescape_z3 = String.substr_replace_all ~pattern:"|" ~with_:""
let rec sort_of env s =
  match Z3.Sort.get_sort_kind s with
  | Z3enums.BOOL_SORT -> T_bool.SBool
  | Z3enums.INT_SORT -> T_int.SInt
  | Z3enums.REAL_SORT -> T_real.SReal
  | Z3enums.DATATYPE_SORT -> begin
      match Set.Poly.find env ~f:(fun (_, sort) -> Stdlib.(s = sort)) with
      | Some (dt, _) -> LogicOld.T_dt.SDT dt
      | _ ->
        if String.is_prefix ~prefix:unint_tuple_prefix @@ unescape_z3 @@ Z3.Sort.to_string s then
          let sorts = List.map ~f:(fun sel -> sort_of env @@ FuncDecl.get_range sel) @@ Tuple.get_field_decls s in
          T_tuple.STuple sorts
        else failwith @@ "[Z3interface.sort_of] unknown dt type:" ^ Z3.Sort.to_string s
    end
  | Z3enums.ARRAY_SORT ->
    T_array.SArray (sort_of env @@ Z3Array.get_domain s, sort_of env @@ Z3Array.get_range s)
  | Z3enums.UNINTERPRETED_SORT ->
    let name = Symbol.get_string @@ Z3.Sort.get_name s in
    if String.is_prefix ~prefix:unint_svar_prefix name then
      let svar = String.sub name ~pos:(String.length unint_svar_prefix) ~len:(String.length name - String.length unint_svar_prefix) in
      Sort.SVar (Ident.Svar svar)
    else if String.(name = unint_string) then T_string.SString
    else if String.(name = unint_finseq) then T_sequence.SFinSequence
    else if String.(name = unint_infseq) then T_sequence.SInfSequence
    else T_dt.SUS (name, [])
  | _ -> (* ToDo: implement other cases *)
    failwith @@ "[Z3interface.sort_of] unknown type:" ^ Z3.Sort.to_string s

let look_up_func_of_dt dt sort func =
  (* Debug.print @@ lazy (sprintf "look_up_func:%d :%s" (Z3.FuncDecl.get_id func) (Z3.FuncDecl.to_string func)); *)
  let id = Z3.FuncDecl.get_id func in
  let conses = Datatype.conses_of dt in
  let z3_conses = Z3.Datatype.get_constructors sort in
  let z3_testers = Z3.Datatype.get_recognizers sort in
  let z3_selss = Z3.Datatype.get_accessors sort in
  let z3_funcs = List.zip3_exn z3_conses z3_testers z3_selss in
  List.fold2_exn conses z3_funcs ~init:`Unkonwn ~f:(fun ret cons (z3_cons, z3_tester, z3_sels) ->
      match ret with
      |`Unkonwn ->
        if id = FuncDecl.get_id z3_cons then `Cons cons
        else if id = FuncDecl.get_id z3_tester then `IsCons cons
        else
          List.fold2_exn (LogicOld.Datatype.sels_of_cons cons) z3_sels ~init:ret ~f:(fun ret sel z3_sel ->
              (* Debug.print @@ lazy (sprintf "search_sel %d =? %d :%s" id (Z3.FuncDecl.get_id z3_sel) (Z3.FuncDecl.to_string z3_sel)); *)
              match ret with
              | `Unkonwn -> if id = FuncDecl.get_id z3_sel then `Sel sel else ret
              | _ -> ret)
      | _ -> ret)
let look_up_func dtenv func =
  Set.Poly.find_map dtenv ~f:(fun (dt, sort) ->
      match look_up_func_of_dt dt sort func with
      | `Unkonwn -> None
      | ret -> Some (dt, ret))

let rec parse_term = function
  | Sexp.Atom "x" ->
    Term.mk_var (Ident.Tvar "x") T_real.SReal
  | Sexp.Atom ident -> begin
      try T_int.mk_int (Z.of_string ident) with _ ->
      try T_real.mk_real (Q.of_string ident) with _ ->
        failwith "[Z3interface.parse_term]"
    end
  | Sexp.List [Sexp.Atom "-"; t] ->
    T_int.mk_neg(*ToDo*) (parse_term t)
  | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
    List.fold args ~init:(parse_term arg) ~f:(fun acc t -> T_int.mk_add(*ToDo*) acc (parse_term t))
  | Sexp.List (Sexp.Atom "*" :: arg :: args) ->
    List.fold args ~init:(parse_term arg) ~f:(fun acc t -> T_int.mk_mult(*ToDo*) acc (parse_term t))
  | Sexp.List [Sexp.Atom "^"; t1; t2] ->
    T_int.mk_power(*ToDo*) (parse_term t1) (parse_term t2)
  | _ -> failwith "[Z3interface.parse_term]"
let parse_root_obj = function
  | Sexp.List [Sexp.Atom "root-obj"; t; n] ->
    let t = parse_term t in t, (int_of_string @@ Sexp.to_string n)
  | e -> failwith @@ "[Z3interface.parse_root_obj]" ^ Sexp.to_string e ^ " is not root-obj"

let var_of s =
  Scanf.unescaped @@ (try Scanf.sscanf s "|%s@|" Fn.id with _ -> s)
  |> Str.split (Str.regexp cache_divide_str)
  |> List.hd_exn

let rec apply senv penv dtenv op expr =
  match List.map ~f:(term_of senv penv dtenv) @@ Expr.get_args expr with
  | e :: es -> List.fold ~init:e es ~f:op
  | _ -> assert false
and apply_bop senv penv dtenv op expr =
  match Expr.get_args expr with
  | [e1; e2] -> op (term_of senv penv dtenv e1) (term_of senv penv dtenv e2)
  | _ -> assert false
and apply_brel senv penv dtenv op expr =
  match Expr.get_args expr with
  | [e1; e2] -> op (term_of senv penv dtenv e1) (term_of senv penv dtenv e2)
  | _ -> assert false
(* from Z3 expr to our term *)
(* term_of: (Ident.tvar, Sort.t) List.Assoc.t -> (Ident.pvar, FuncDecl.func_decl) List.Assoc.t -> Z3.Expr.expr -> info Logic.term *)
and term_of (senv: (Ident.tvar, Sort.t) List.Assoc.t) (penv: (Ident.pvar, FuncDecl.func_decl) List.Assoc.t) (dtenv:dtenv) expr = (*try*)
  Debug.print @@ lazy ("[Z3interface.term_of] " ^ Z3.Expr.to_string expr);
  if Boolean.is_true expr then
    T_bool.of_atom @@ Atom.mk_true ()
  else if Boolean.is_false expr then
    T_bool.of_atom @@ Atom.mk_false ()
  else if Boolean.is_ite expr then
    match Expr.get_args expr with
    | [e1; e2; e3] ->
      T_bool.ifte (formula_of senv penv dtenv e1) (term_of senv penv dtenv e2) (term_of senv penv dtenv e3)
    | _ -> assert false
  else if Arithmetic.is_int_numeral expr then
    T_int.mk_int (Arithmetic.Integer.get_big_int expr)
  else if Arithmetic.is_rat_numeral expr then
    T_real.mk_real (Arithmetic.Real.get_ratio expr)
  else if Arithmetic.is_algebraic_number expr then
    let expr = Sexp.of_string @@ Expr.to_string expr in
    let t, n = parse_root_obj expr in
    T_real.mk_alge t n
  else if Arithmetic.is_add expr then
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_int.SInt -> apply senv penv dtenv T_int.mk_add expr
    | T_real.SReal -> apply senv penv dtenv T_real.mk_radd expr
    | _ -> failwith @@ "[Z3interface.term_of]" ^ Z3.Sort.to_string @@ Expr.get_sort expr
  else if Arithmetic.is_sub expr then
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_int.SInt -> apply senv penv dtenv T_int.mk_sub expr
    | T_real.SReal -> apply senv penv dtenv T_real.mk_rsub expr
    | _ -> failwith @@ "[Z3interface.term_of]" ^ Z3.Sort.to_string @@ Expr.get_sort expr
  else if Arithmetic.is_mul expr then
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_int.SInt -> apply senv penv dtenv T_int.mk_mult expr
    | T_real.SReal -> apply senv penv dtenv T_real.mk_rmult expr
    | _ -> failwith @@ "[Z3interface.term_of]" ^ Z3.Sort.to_string @@ Expr.get_sort expr
  else if Arithmetic.is_idiv expr then
    apply_bop senv penv dtenv T_int.mk_div expr
  else if Arithmetic.is_div expr then
    apply_bop senv penv dtenv T_real.mk_rdiv expr
  else if Arithmetic.is_modulus expr then
    apply_bop senv penv dtenv T_int.mk_mod expr
  else if Arithmetic.is_remainder expr then
    apply_bop senv penv dtenv T_int.mk_rem expr
  else if AST.is_var @@ Expr.ast_of_expr expr then (* bound variables *)
    let _ = Debug.print @@ lazy ("z3 bound var: " ^ Expr.to_string expr) in
    try
      let tvar, sort =
        List.nth_exn senv @@
        List.length senv - Scanf.sscanf (Expr.to_string expr) "(:var %d)" Fn.id - 1
      in
      Term.mk_var tvar sort
    with _ -> failwith @@ "[Z3interface.term_of] " ^ Expr.to_string expr ^ " not found"
  else if Z3Array.is_store expr then
    let sa = sort_of dtenv @@ Expr.get_sort expr in
    match List.map ~f:(term_of senv penv dtenv) @@ Expr.get_args expr, sa with
    | [t1; t2; t3], T_array.SArray (s1, s2) -> T_array.mk_store s1 s2 t1 t2 t3
    | _ -> failwith "[Z3interface.term_of]"
  else if Z3Array.is_constant_array expr then
    let sa = sort_of dtenv @@ Expr.get_sort expr in
    match List.map ~f:(term_of senv penv dtenv) @@ Expr.get_args expr, sa with
    | [t1], T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 t1
    | _ -> failwith "[Z3interface.term_of]"
  else if Z3Array.is_select expr then
    let args = Expr.get_args expr in
    match args, List.map ~f:(term_of senv penv dtenv) args with
    | [e1; _e2], [t1; t2] -> begin
        match T_array.eval_select t1 t2, sort_of dtenv @@ Expr.get_sort e1 with
        | Some te, _ -> te
        | _, T_array.SArray (s1, s2) -> T_array.mk_select s1 s2 t1 t2
        | _ -> failwith "[Z3interface.term_of]"
      end
    | _ -> failwith "[Z3interface.term_of]"
  else (* applications (and constants) *)
    try
      let func = Z3.Expr.get_func_decl expr in
      let name =
        FuncDecl.get_name func
        |> Symbol.get_string
        |> unescape_z3
        |> Str.split (Str.regexp cache_divide_str)
        |> List.hd_exn
      in
      let ts = List.map ~f:(term_of senv penv dtenv) @@ Z3.Expr.get_args expr in
      let sorts = List.map ~f:Term.sort_of ts in
      (* the following causes an exception if [expr] contains a bound variable:
         let sorts = List.map ~f:(fun e -> sort_of dtenv @@ Expr.get_sort e) @@ Z3.Expr.get_args expr in *)
      let sort = sort_of dtenv @@ FuncDecl.get_range func in
      try (* algebraic data types *)
        Debug.print @@ lazy (sprintf "[Z3interface.term_of] %s" @@ Z3.Expr.to_string expr);
        match look_up_func dtenv func with
        | Some (dt, `Cons cons) ->
          T_dt.mk_cons dt (Datatype.name_of_cons cons) ts
        | Some (dt, `IsCons cons) ->
          T_bool.of_atom @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) @@ List.hd_exn ts
        | Some (dt, `Sel sel) ->
          T_dt.mk_sel dt (Datatype.name_of_sel sel) @@ List.hd_exn ts
        | None when T_dt.is_sdt sort && List.is_empty ts ->
          Term.mk_var (Ident.Tvar name) sort
        | _ -> failwith "[Z3interface.term_of] not an ADT term"
      with _ ->
      try (* tuples *)
        if String.is_prefix ~prefix:unint_tuple_prefix name then
          T_tuple.mk_tuple_cons sorts ts
        else if String.is_prefix ~prefix:unint_tuple_sel_prefix name && List.length ts = 1 then
          let pre_length = String.length unint_tuple_sel_prefix in
          let i = Int.of_string @@ String.sub name ~pos:pre_length ~len:(String.length name - pre_length) in
          match ts, sorts with
          | [t], [T_tuple.STuple sorts] -> T_tuple.mk_tuple_sel sorts t i
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.(name = "is"(*ToDo: Z3 automatically generates a tester of the name*)) && List.length ts = 1 then
          match ts, sorts with
          | [_t], [T_tuple.STuple _sorts] ->
            (*ToDo*)T_bool.mk_true ()(*T_bool.of_atom @@ T_tuple.mk_is_tuple sorts t*)
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.is_prefix ~prefix:unint_string_prefix name && List.is_empty ts then
          let pre_length = String.length unint_string_prefix in
          let str = String.sub name ~pos:pre_length ~len:(String.length name - pre_length) in
          T_string.mk_string_const str
        else if String.(name = unint_epsilon) && List.is_empty ts then
          T_sequence.mk_eps ()
        else if String.is_prefix ~prefix:unint_symbol_prefix name && List.is_empty ts then
          let pre_length = String.length unint_symbol_prefix in
          let symbol = String.sub name ~pos:pre_length ~len:(String.length name - pre_length) in
          T_sequence.mk_symbol symbol
        else if String.(name = unint_concat_fin) then
          match ts with
          | [t1; t2] -> T_sequence.concat ~fin:true t1 t2
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.(name = unint_concat_inf) && List.length ts = 2 then
          match ts with
          | [t1; t2] -> T_sequence.concat ~fin:false t1 t2
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.is_prefix ~prefix:unint_is_prefix_of_fin name then
          match ts with
          | [t1; t2] -> T_bool.of_atom @@ T_sequence.mk_is_prefix true t1 t2
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.is_prefix ~prefix:unint_is_prefix_of_inf name && List.length ts = 2 then
          match ts with
          | [t1; t2] -> T_bool.of_atom @@ T_sequence.mk_is_prefix false t1 t2
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.is_prefix ~prefix:unint_is_in_reg_exp_fin_prefix name then
          let regexp = failwith "not supported" in
          match ts with
          | [t] -> T_bool.of_atom @@ T_sequence.mk_is_in_regexp true regexp t
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else if String.is_prefix ~prefix:unint_is_in_reg_exp_inf_prefix name then
          let regexp = failwith "not supported" in
          match ts with
          | [t] -> T_bool.of_atom @@ T_sequence.mk_is_in_regexp false regexp t
          | _ -> failwith "[Z3interface.term_of] not a valid tuple/string/sequence term"
        else failwith "[Z3interface.term_of] not a tuple/string/sequence term"
      with _ ->
      match Map.Poly.find (Atomic.get ref_fenv) (Ident.Tvar name) with
      | Some (params, ret_sort, _, _, _) ->
        Term.mk_fvar_app (Ident.Tvar name) (List.map params ~f:snd @ [ret_sort](*sorts @ [sort]*)) ts
      | _ ->
        try(*ToDo*)
          match sort_of dtenv @@ Expr.get_sort expr with
          | T_bool.SBool -> T_bool.of_formula @@ formula_of senv penv dtenv expr
          | _ -> failwith "[Z3interface.term_of] not a formula"
        with _ ->
          if List.is_empty ts then Term.mk_var (Ident.Tvar name) sort
          else LogicOld.Term.mk_fvar_app (Ident.Tvar name) (sorts @ [sort]) ts
    with Failure err ->
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_bool.SBool -> T_bool.of_formula @@ formula_of senv penv dtenv expr
    | _ -> failwith @@ sprintf "[Z3interface.term_of] %s : %s" err @@ Z3.Expr.to_string expr
and
  (* from Z3 expr to our atom *)
  (* atom_of: (Ident.tvar, Sort.t) List.Assoc.t -> (Ident.pvar, FuncDecl.func_decl) List.Assoc.t -> Z3.Expr.expr -> info Logic.Atom.t *)
  atom_of
    (senv : (Ident.tvar, Sort.t) List.Assoc.t)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (dtenv : dtenv)
    expr =
  (* Debug.print @@ lazy ("[z3:atom_of] " ^ Z3.Expr.to_string expr); *)
  if Boolean.is_true expr then
    Atom.mk_true ()
  else if Boolean.is_false expr then
    Atom.mk_false ()
  else if Boolean.is_eq expr then
    apply_brel senv penv dtenv T_bool.mk_eq expr
  else if Arithmetic.is_le expr then
    Typeinf.typeinf_atom @@ apply_brel senv penv dtenv T_num.mk_nleq expr
  else if Arithmetic.is_ge expr then
    Typeinf.typeinf_atom @@ apply_brel senv penv dtenv T_num.mk_ngeq expr
  else if Arithmetic.is_lt expr then
    Typeinf.typeinf_atom @@ apply_brel senv penv dtenv T_num.mk_nlt expr
  else if Arithmetic.is_gt expr then
    Typeinf.typeinf_atom @@ apply_brel senv penv dtenv T_num.mk_ngt expr
  else if AST.is_var @@ Expr.ast_of_expr expr then (* bound variables *)
    let tvar, _sort(* assume bool*) =
      List.nth_exn senv @@
      List.length senv - Scanf.sscanf (Expr.to_string expr) "(:var %d)" Fn.id - 1
    in
    match List.Assoc.find ~equal:Stdlib.(=) penv (Ident.tvar_to_pvar tvar) with
    | Some _ -> Atom.mk_pvar_app (Ident.tvar_to_pvar tvar) [] []
    | _ -> Atom.of_bool_term @@ Term.mk_var tvar T_bool.SBool
  else
    let func = Z3.Expr.get_func_decl expr in
    let name =
      FuncDecl.get_name func
      |> Symbol.get_string
      |> unescape_z3
      |> Str.split (Str.regexp cache_divide_str)
      |> List.hd_exn
    in
    let pvar = Ident.Pvar name in
    let ts = List.map ~f:(term_of senv penv dtenv) @@ Z3.Expr.get_args expr in
    match List.Assoc.find ~equal:Stdlib.(=) penv pvar with
    | Some _ -> Atom.mk_pvar_app pvar (List.map ts ~f:Term.sort_of) ts
    | None ->
      try Atom.of_bool_term @@ term_of senv penv dtenv expr with _ ->
        failwith @@ "[Z3interface.atom_of] " ^ Z3.Expr.to_string expr
and
  (* from Z3 expr to our formula *)
  (* formula_of: (Ident.tvar, Sort.t) List.Assoc.t -> (Ident.pvar, FuncDecl.func_decl) List.Assoc.t -> Z3.Expr.expr -> info Logic.Formula.t *)
  formula_of
    (senv : (Ident.tvar, Sort.t) List.Assoc.t)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (dtenv : dtenv)
    expr =
  (* Debug.print @@ lazy ("[Z3interface.formula_of] " ^ Z3.Expr.to_string expr); *)
  if Boolean.is_not expr then
    match Expr.get_args expr with
    | [body] -> Formula.negate (formula_of senv penv dtenv body)
    | _ -> failwith "[Z3interface.formula_of]"
  else if Boolean.is_and expr then
    Formula.and_of @@ List.map ~f:(formula_of senv penv dtenv) @@ Expr.get_args expr
  else if Boolean.is_or expr then
    Formula.or_of @@ List.map ~f:(formula_of senv penv dtenv) @@ Expr.get_args expr
  else if Boolean.is_iff expr then
    Expr.get_args expr
    |> List.map ~f:(formula_of senv penv dtenv)
    |> function [phi1; phi2] -> Formula.mk_iff phi1 phi2
              | _ -> failwith "[Z3interface.formula_of]"
  else if Boolean.is_implies expr then
    Expr.get_args expr
    |> List.map ~f:(formula_of senv penv dtenv)
    |> function [phi1; phi2] -> Formula.mk_imply phi1 phi2
              | _ -> failwith "[Z3interface.formula_of]"
  else if Boolean.is_ite expr then
    match Expr.get_args expr with
    | [e1; e2; e3] ->
      Formula.of_bool_term @@
      T_bool.ifte (formula_of senv penv dtenv e1) (term_of senv penv dtenv e2) (term_of senv penv dtenv e3)
    | _ -> failwith "[Z3interface.formula_of]"
  else if AST.is_quantifier @@ Expr.ast_of_expr expr then
    let q = Quantifier.quantifier_of_expr expr in
    let binder = if Quantifier.is_universal q then Formula.Forall else Formula.Exists in
    let bounds =
      List.zip_exn
        (List.map ~f:(fun x -> Ident.Tvar (Symbol.get_string x)) @@
         Quantifier.get_bound_variable_names q)
        (List.map ~f:(sort_of dtenv) @@ Quantifier.get_bound_variable_sorts q)
    in
    let senv = bounds @ senv in
    Formula.mk_bind binder bounds @@
    formula_of senv penv dtenv @@ Quantifier.get_body q
  else Formula.mk_atom @@ atom_of senv penv dtenv expr

let dummy_term_map_of terms =
  Map.of_set_exn @@ Set.Poly.filter_map terms ~f:(function (tvar, (T_dt.SUS _ as sort)) ->
      Some (tvar, mk_fresh_dummy_term sort) | _ -> None)

let add_dummy_term model =
  List.filter_map model ~f:(function _, Some t -> Some t | _ -> None)
  |> List.fold_left ~init:Set.Poly.empty ~f:(fun ret term ->
      Set.Poly.filter ~f:(function (_, T_dt.SUS _) -> true | _ -> false) @@
      Set.Poly.union ret @@ Term.term_sort_env_of term)
  |> Set.Poly.iter ~f:(fun (tvar, sort) -> add_dummy_term tvar sort)

let model_of dtenv model =
  let model =
    List.map (Model.get_decls model) ~f:(fun decl ->
        let x =
          FuncDecl.get_name decl
          |> Symbol.get_string
          |> Str.split (Str.regexp cache_divide_str)
          |> List.hd_exn
        in
        let s =
          Sort.mk_fun @@
          List.map ~f:(sort_of dtenv) @@
          FuncDecl.get_domain decl @ [FuncDecl.get_range decl]
        in
        (Ident.Tvar x, s),
        if FuncDecl.get_arity decl = 0 then
          match Model.get_const_interp model decl with
          | Some expr -> Some (term_of [] [] dtenv expr)
          | None -> None
        else
          match Model.get_func_interp model decl with
          | Some _func -> None(*ToDo*)
          | None -> None)
  in
  Debug.print @@ lazy ("model is :" ^ LogicOld.str_of_model model);
  model

(** encoding *)

let of_var ctx (Ident.Tvar var) = var |> String.escaped |> Symbol.mk_string ctx

let list_type s ctx = Z3List.mk_sort ctx (Symbol.mk_string ctx "list") s
let array_type t1 t2 ctx = Z3Array.mk_sort ctx t1 t2
let sorts_of_tuple sort = sort |> Tuple.get_mk_decl |> FuncDecl.get_domain

(* from our sort to Z3 sort *)

let str_of_z3_env env =
  Set.Poly.fold env ~init:"z3_env:" ~f:(fun ret (dt, sort) ->
      ret ^ "\nLogicOld:\n" ^
      LogicOld.Datatype.str_of dt ^ "Z3:\n" ^ Z3.Sort.to_string sort ^
      List.fold2_exn
        (Z3.Datatype.get_constructors sort)
        (Z3.Datatype.get_accessors sort)
        ~init:"" ~f:(fun ret cons sels ->
            ret ^ sprintf "\n|%d: %s" (Z3.FuncDecl.get_id cons) (Z3.FuncDecl.to_string cons) ^
            List.fold_left sels ~init:"" ~f:(fun ret sel ->
                ret ^ "\n>>> " ^ sprintf "%d: %s" (Z3.FuncDecl.get_id sel) (Z3.FuncDecl.to_string sel))) ^
      List.fold_left
        (Z3.Datatype.get_recognizers sort)
        ~init:"\ntesters:" ~f:(fun ret iscons ->
            ret ^ "\n ?" ^ sprintf "%d: %s" (Z3.FuncDecl.get_id iscons) (Z3.FuncDecl.to_string iscons)))

let rec of_sort ctx dtenv = function
  | Sort.SVar (Ident.Svar svar) ->
    Z3.Sort.mk_uninterpreted_s ctx @@ unint_svar_prefix ^ svar
  (*| Sort.SArrow (s1, (s2, Sort.Pure)) ->
    Z3Array.mk_sort ctx (of_sort ctx dtenv s1) (of_sort ctx dtenv s2)*)
  | Sort.SArrow (_, (_, _, _)) as s ->
    Z3.Sort.mk_uninterpreted_s ctx (Term.str_of_sort s)
  | T_bool.SBool ->
    Boolean.mk_sort ctx
  | T_int.SInt ->
    Arithmetic.Integer.mk_sort ctx
  | T_real.SReal ->
    Arithmetic.Real.mk_sort ctx
  | T_tuple.STuple sorts ->
    tuple_sort_of ctx dtenv sorts
  | T_dt.SUS (name, []) ->
    Z3.Sort.mk_uninterpreted_s ctx name
  | T_dt.SUS (_name, _params) -> (*ToDo*)
    Z3.Sort.mk_uninterpreted_s ctx "unsupported"
  (*Z3.Sort.mk_uninterpreted_s ctx (name ^ "_with_args")*)
  (*("(" ^ (String.concat_map_list ~sep:"," params ~f:Term.str_of_sort) ^ ") " ^ name)*)
  | T_dt.SDT dt -> begin
      match Set.Poly.find dtenv ~f:(fun (dt1, _) ->
          Stdlib.(LogicOld.Datatype.full_name_of dt1 = LogicOld.Datatype.full_name_of dt)) with
      | Some (_, sort) -> sort
      | None ->
        Debug.print @@ lazy
          (sprintf "[Z3interface.of_sort] %s to %s"
             (Term.str_of_sort @@ T_dt.SDT dt) (str_of_z3_env dtenv));
        of_sort ctx (update_z3env ctx dtenv dt) (T_dt.SDT dt)
    end
  | T_array.SArray (si, se) ->
    Z3Array.mk_sort ctx (of_sort ctx dtenv si) (of_sort ctx dtenv se)
  | T_string.SString -> Z3.Sort.mk_uninterpreted_s ctx unint_string
  | T_sequence.SFinSequence -> Z3.Sort.mk_uninterpreted_s ctx unint_finseq
  | T_sequence.SInfSequence -> Z3.Sort.mk_uninterpreted_s ctx unint_infseq
  | sort ->
    failwith @@ sprintf "[Z3interface.of_sort] %s is unknown" @@ LogicOld.Term.str_of_sort sort
and tuple_sort_of ctx dtenv sorts =
  let tuple_num = List.length sorts in
  Tuple.mk_sort ctx
    (Symbol.mk_string ctx @@ sprintf "%s(%s)" unint_tuple_prefix (*tuple_num*) @@
     String.concat_map_list ~sep:"," ~f:Term.short_name_of_sort sorts)
    (* (tuple_prefix ^ string_of_int tuple_num |> Idnt.make |> sym_of_var) *)
    (List.init tuple_num ~f:(fun i -> Symbol.mk_string ctx @@ unint_tuple_sel_prefix ^ string_of_int i))
    (List.map sorts ~f:(of_sort ctx dtenv))
and update_z3env ctx dtenv t =
  let dts = LogicOld.Datatype.full_dts_of t in
  let dt_names, dt_conses =
    List.unzip @@
    List.map dts ~f:(fun dt ->
        LogicOld.Datatype.full_name_of_dt dt,
        List.map (LogicOld.Datatype.conses_of_dt dt) ~f:(fun cons ->
            let name = LogicOld.Datatype.name_of_cons cons in
            Debug.print @@ lazy (sprintf "mk cons:[%s]" name);
            let is_cons_name = Z3.Symbol.mk_string ctx @@ unint_is_cons_prefix ^ name in
            Debug.print @@ lazy (sprintf "mk is_cons:[%s]" @@ Z3.Symbol.get_string is_cons_name);
            let sels_names, ret_sorts, ref_sorts =
              List.fold_left (LogicOld.Datatype.sels_of_cons cons) ~init:([], [], [])
                ~f:(fun (sels_names, ret_sorts, ref_sorts) -> function
                    | LogicOld.Datatype.Sel (name, ret_sort) ->
                      Debug.print @@ lazy (sprintf "mk sel:[%s]" name);
                      Z3.Symbol.mk_string ctx name :: sels_names,
                      (Some (of_sort ctx dtenv ret_sort)) :: ret_sorts,
                      0 :: ref_sorts
                    | LogicOld.Datatype.InSel (name, ret_name, args) ->
                      Debug.print @@ lazy (sprintf "mk insel:[%s]" name);
                      let full_name =
                        List.fold_left args ~init:ret_name
                          ~f:(fun ret arg -> ret ^ LogicOld.Term.str_of_sort arg)
                      in
                      match Set.Poly.find dtenv ~f:(fun (dt, _) ->
                          Stdlib.(full_name = LogicOld.Datatype.full_name_of dt)) with
                      | Some (_, sort) ->
                        Z3.Symbol.mk_string ctx name :: sels_names,
                        (Some sort) :: ret_sorts,
                        0 :: ref_sorts
                      | None ->
                        match List.findi dts ~f:(fun _ dt ->
                            Stdlib.(LogicOld.Datatype.name_of_dt dt = ret_name)) with
                        | Some (i, _) ->
                          (* Debug.print @@ lazy (sprintf "ref id:%d" i); *)
                          Z3.Symbol.mk_string ctx name :: sels_names,
                          None :: ret_sorts,
                          i :: ref_sorts
                        | _ -> assert false)
            in
            let z3cons =
              Z3.Datatype.mk_constructor ctx
                (Z3.Symbol.mk_string ctx name)
                is_cons_name
                (List.rev sels_names)
                (List.rev ret_sorts)
                (List.rev ref_sorts)
            in
            (* Debug.print @@ lazy ("z3 tester: " ^ Z3.Datatype.Constructor.get_tester_decl z3cons |> Z3.FuncDecl.to_string); *)
            (* List.iter (Z3.Datatype.Constructor.get_accessor_decls z3cons) ~f:(fun sel ->
               Debug.print @@ lazy ("z3 sel:" ^ Z3.FuncDecl.to_string sel)); *)
            z3cons))
  in
  Z3.Datatype.mk_sorts_s ctx dt_names dt_conses
  |> List.fold2_exn dts ~init:dtenv ~f:(fun dtenv dt sort ->
      Set.Poly.add dtenv (LogicOld.Datatype.update_name (LogicOld.Datatype.update_dts t dts) @@ LogicOld.Datatype.name_of_dt dt, sort))
and z3_dtenv_of_dtenv ?(init=Set.Poly.empty) ctx dtenv =
  (* Debug.print @@ lazy ("mk z3 dtenv from:\n" ^ LogicOld.DTEnv.str_of dtenv); *)
  let z3_dtenv =
    Map.Poly.fold dtenv ~init ~f:(fun ~key:_ ~data env ->
        (* Debug.print @@ lazy (sprintf "mk sort:%s \n%s" key (LogicOld.Datatype.str_of data)); *)
        if Set.Poly.exists env ~f:(fun (dt, _) ->
            Stdlib.(LogicOld.Datatype.full_name_of data = LogicOld.Datatype.full_name_of dt))
        then env
        else update_z3env ctx env data)
  in
  (* Debug.print @@ lazy (str_of_z3_env z3_dtenv); *)
  z3_dtenv
let z3_dtenv_of ?(init=Set.Poly.empty) ctx phi =
  LogicOld.update_ref_dtenv @@ LogicOld.DTEnv.of_formula phi;
  let dtenv = Atomic.get LogicOld.ref_dtenv in
  Debug.print @@ lazy ("[Z3interface.z3_dtenv_of] from:\n" ^ LogicOld.DTEnv.str_of dtenv);
  z3_dtenv_of_dtenv ~init ctx dtenv
let z3_dt_of (dtenv:dtenv) dt =
  try
    snd @@ Set.Poly.find_exn dtenv ~f:(fun (dt1, _) ->
        (*print_endline @@ sprintf "%s" (LogicOld.Datatype.full_name_of dt1);*)
        Stdlib.(LogicOld.Datatype.full_name_of dt = LogicOld.Datatype.full_name_of dt1))
  with _ ->
    failwith @@ sprintf "[Z3interface.z3_dt_of] %s not found" (LogicOld.Datatype.full_name_of dt)
let z3_cons_of (dtenv:dtenv) dt name =
  let z3_conses = Z3.Datatype.get_constructors @@ z3_dt_of dtenv dt in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_conses) ~f:(fun (cons, z3_cons) ->
      if Stdlib.(Datatype.name_of_cons cons = name) then Some z3_cons else None)
let z3_sel_of (dtenv:dtenv) dt name =
  let z3_selss = Z3.Datatype.get_accessors @@ z3_dt_of dtenv dt in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_selss) ~f:(fun (cons, z3_sels) ->
      let sels = Datatype.sels_of_cons cons in
      List.find_map (List.zip_exn sels z3_sels) ~f:(fun (sel, z3_sel) ->
          if Stdlib.(name = Datatype.name_of_sel sel) then Some z3_sel else None))
let z3_iscons_of (dtenv:dtenv) dt name =
  let z3_testers = Z3.Datatype.get_recognizers @@ z3_dt_of dtenv dt in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_testers) ~f:(fun (cons, z3_tester) ->
      if Stdlib.(Datatype.name_of_cons cons = name) then Some z3_tester else None)

let z3_string_of ctx str =
  FuncDecl.mk_func_decl_s ctx (unint_string_prefix ^ str(*ToDo: need to avoid escaping by z3?*)) [] @@
  Z3.Sort.mk_uninterpreted_s ctx unint_string
let z3_epsilon ctx = 
  FuncDecl.mk_func_decl_s ctx unint_epsilon [] @@
  Z3.Sort.mk_uninterpreted_s ctx unint_finseq
let z3_symbol_of ctx str =
  FuncDecl.mk_func_decl_s ctx (unint_symbol_prefix ^ str(*ToDo: need to avoid escaping by z3?*)) [] @@
  Z3.Sort.mk_uninterpreted_s ctx unint_finseq
let z3_concat ctx fin =
  let sort =
    if fin then Z3.Sort.mk_uninterpreted_s ctx unint_finseq
    else Z3.Sort.mk_uninterpreted_s ctx unint_infseq
  in
  FuncDecl.mk_func_decl_s ctx (if fin then unint_concat_fin else unint_concat_inf)
    [Z3.Sort.mk_uninterpreted_s ctx unint_finseq; sort] sort
let z3_is_prefix_of ctx fin =
  FuncDecl.mk_func_decl_s ctx
    (if fin then unint_is_prefix_of_fin else unint_is_prefix_of_inf)
    [Z3.Sort.mk_uninterpreted_s ctx unint_finseq;
     if fin then Z3.Sort.mk_uninterpreted_s ctx unint_finseq
     else Z3.Sort.mk_uninterpreted_s ctx unint_infseq]
    (Boolean.mk_sort ctx)
let z3_is_in_reg_exp ctx fin regexp =
  FuncDecl.mk_func_decl_s ctx
    (if fin then unint_is_in_reg_exp_fin_prefix ^ "(" ^ Grammar.RegWordExp.str_of Fn.id regexp ^ ")"
     else unint_is_in_reg_exp_inf_prefix ^ "(" ^ Grammar.RegWordExp.str_of Fn.id regexp ^ ")")
    [if fin then Z3.Sort.mk_uninterpreted_s ctx unint_finseq
     else Z3.Sort.mk_uninterpreted_s ctx unint_infseq]
    (Boolean.mk_sort ctx)

let penv_of phi ctx dtenv =
  Formula.pred_sort_env_of phi
  |> Set.Poly.to_list
  |> List.map ~f:(fun (pvar, sorts) ->
      pvar,
      FuncDecl.mk_func_decl_s ctx
        (Ident.name_of_pvar pvar)
        (List.map sorts ~f:(of_sort ctx dtenv))
        (Boolean.mk_sort ctx))

(* from our formula to Z3 expr *)
(* of_formula: Z3.context -> (Ident.tvar, Sort.t) List.Assoc.t -> info Logic.Formula.t *)
let rec of_formula ctx
    (env : sort_env_list)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (fenv : fenv)
    (dtenv : (LogicOld.Datatype.t *Z3.Sort.sort) Set.Poly.t)
    phi =
  (* Debug.print @@ lazy ("[Z3interface.of_formula] " ^ Formula.str_of phi); *)
  if Formula.is_atom phi then
    let atom, _ = Formula.let_atom phi in
    if Atom.is_pvar_app atom then
      let pvar, sorts, _, _ = Atom.let_pvar_app atom in
      (* Debug.print @@ lazy ("is_pvar_app: " ^ Formula.str_of phi); *)
      let func =
        FuncDecl.mk_func_decl_s ctx
          (Ident.name_of_pvar pvar)
          (List.map sorts ~f:(of_sort ctx dtenv))
          (Boolean.mk_sort ctx)
      in
      let penv = if not @@ List.Assoc.mem ~equal:Stdlib.(=) penv pvar then (pvar, func) :: penv else penv in
      of_atom ctx env penv fenv dtenv atom
    else of_atom ctx env penv fenv dtenv atom
  else if Formula.is_neg phi then
    Boolean.mk_not ctx @@ of_formula ctx env penv fenv dtenv @@ fst (Formula.let_neg phi)
  else if Formula.is_and phi then
    let phi1, phi2, _ = Formula.let_and phi in
    Boolean.mk_and ctx
      [of_formula ctx env penv fenv dtenv phi1;
       of_formula ctx env penv fenv dtenv phi2]
  else if Formula.is_or phi then
    let phi1, phi2, _ = Formula.let_or phi in
    Boolean.mk_or ctx
      [of_formula ctx env penv fenv dtenv phi1;
       of_formula ctx env penv fenv dtenv phi2]
  else if Formula.is_iff phi then
    let phi1, phi2, _ = Formula.let_iff phi in
    Boolean.mk_iff ctx
      (of_formula ctx env penv fenv dtenv phi1)
      (of_formula ctx env penv fenv dtenv phi2)
  else if Formula.is_imply phi then
    let phi1, phi2, _ = Formula.let_imply phi in
    Boolean.mk_implies ctx
      (of_formula ctx env penv fenv dtenv phi1)
      (of_formula ctx env penv fenv dtenv phi2)
  else if Formula.is_bind phi then
    let binder, bounds, body, _ = Formula.let_bind phi in
    let bounds = List.rev bounds in
    let env = bounds @ env in
    let sorts = List.map bounds ~f:(fun (_, sort) -> of_sort ctx dtenv sort) in
    let vars = List.map bounds ~f:(fun (var, _) -> of_var ctx var) in
    let body = of_formula ctx env penv fenv dtenv body in
    (match binder with
     | Formula.Forall -> Quantifier.mk_forall ctx sorts vars body None [] [] None None
     | Formula.Exists -> Quantifier.mk_exists ctx sorts vars body None [] [] None None
     | _ -> assert false)
    |> Quantifier.expr_of_quantifier
    |> (fun e -> add_to_bound_var_cache e; e)
  else if Formula.is_letrec phi then
    match Formula.let_letrec phi with
    | [], phi, _ -> of_formula ctx env penv fenv dtenv phi
    | _, _, _ ->
      failwith @@ "[Z3interface.of_formula] underlying solver cannot deal with fixpoint predicates: " ^ Formula.str_of phi;
  else failwith @@ sprintf "[Z3interface.of_formula] %s not supported: " @@ Formula.str_of phi

and of_var_term ctx env dtenv t =
  let (var, sort), _ = Term.let_var t in
  (* Debug.print @@ lazy
     (sprintf "z3_of_var_term:%s %s"
     (Ident.name_of_tvar var) (Term.str_of_sort @@ Term.sort_of t)); *)
  match List.findi env ~f:(fun _ (key, _) -> Stdlib.(key = var)) with
  | Some (i, (_, sort')) ->
    assert Stdlib.(sort = sort');
    (* Debug.print @@ lazy ("mk quantifier"); *)
    let sort = of_sort ctx dtenv sort in
    (* lock (); (fun ret -> unlock (); ret) @@   *)
    Quantifier.mk_bound ctx i sort
  | None ->
    find_in_cache ctx env t ~f:(fun cid ->
        let name = Ident.name_of_tvar var in
        let symbol =
          of_var ctx @@
          Ident.Tvar (sprintf "%s%s%d%s" name cache_divide_str cid (Term.short_name_of_sort sort))
        in
        let sort = of_sort ctx dtenv sort in
        (* print_endline @@ ("mk const var" ^ (Ident.name_of_tvar var)); *)
        Expr.mk_const ctx symbol sort)

(* from our term to Z3 expr *)
and of_term ctx
    (env : (Ident.tvar, Sort.t) List.Assoc.t)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (fenv : fenv)
    (dtenv : (LogicOld.Datatype.t * Z3.Sort.sort) Set.Poly.t) t =
  Debug.print @@ lazy (sprintf "[Z3interface.of_term] %s" @@ Term.str_of t);
  if Term.is_var t then
    of_var_term ctx env dtenv t
  else if Term.is_app t then
    match Term.let_app t with
    | T_bool.Formula phi, [], _ ->
      of_formula ctx env penv fenv dtenv phi
    | T_bool.IfThenElse, [cond; then_; else_], _ ->
      Boolean.mk_ite ctx
        (of_term ctx env penv fenv dtenv cond)
        (of_term ctx env penv fenv dtenv then_)
        (of_term ctx env penv fenv dtenv else_)
    | T_int.Int n, [], _ ->
      find_in_cache ctx env t ~f:(fun _ ->
          Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n))
    | T_real.Real r, [], _ ->
      find_in_cache ctx env t ~f:(fun _ ->
          Arithmetic.Real.mk_numeral_s ctx (Q.to_string r))
    | (T_int.Add | T_real.RAdd), [t1; t2], _ ->
      Arithmetic.mk_add ctx
        [of_term ctx env penv fenv dtenv t1;
         of_term ctx env penv fenv dtenv t2]
    | (T_int.Sub | T_real.RSub), [t1; t2], _ ->
      Arithmetic.mk_sub ctx
        [of_term ctx env penv fenv dtenv t1;
         of_term ctx env penv fenv dtenv t2]
    | (T_int.Mult | T_real.RMult), [t1; t2], _ ->
      Arithmetic.mk_mul ctx
        [of_term ctx env penv fenv dtenv t1;
         of_term ctx env penv fenv dtenv t2]
    | T_int.Div, [t1; t2], _ ->
      Arithmetic.mk_div ctx
        (of_term ctx env penv fenv dtenv t1)
        (of_term ctx env penv fenv dtenv t2)
    | T_int.Mod, [t1; t2], _ ->
      Arithmetic.Integer.mk_mod ctx
        (of_term ctx env penv fenv dtenv t1)
        (of_term ctx env penv fenv dtenv t2)
    | T_int.Rem, [t1; t2], _ ->
      Arithmetic.Integer.mk_rem ctx
        (of_term ctx env penv fenv dtenv t1)
        (of_term ctx env penv fenv dtenv t2)
    | T_real.RDiv, [t1; t2], _ ->
      Arithmetic.mk_div ctx
        (Arithmetic.Integer.mk_int2real(*ToDo: remove*) ctx @@
         of_term ctx env penv fenv dtenv t1)
        (Arithmetic.Integer.mk_int2real(*ToDo: remove*) ctx @@
         of_term ctx env penv fenv dtenv t2)
    | (T_int.Neg | T_real.RNeg), [t1], _ when Term.is_var t1 || T_int.is_int t1 ->
      let n = of_term ctx env penv fenv dtenv t1 in
      if T_int.is_int t1 || Expr.is_const n then
        find_in_cache ctx env t ~f:(fun _ -> Arithmetic.mk_unary_minus ctx n)
      else Arithmetic.mk_unary_minus ctx n
    | (T_int.Neg | T_real.RNeg), [t], _ ->
      Arithmetic.mk_unary_minus ctx (of_term ctx env penv fenv dtenv t)
    | (T_int.Abs | T_real.RAbs) as op, [t], _ ->
      let n = of_term ctx env penv fenv dtenv t in
      let minus_n = of_term ctx env penv fenv dtenv (T_int.mk_neg t) in
      let is_minus =
        Arithmetic.mk_lt ctx n
          (match op with
           | T_int.Abs ->
             find_in_cache ctx env (T_int.zero ())
               ~f:(fun _ -> Arithmetic.Integer.mk_numeral_i ctx 0)
           | T_real.RAbs ->
             find_in_cache ctx env (T_real.rzero ())
               ~f:(fun _ -> Arithmetic.Real.mk_numeral_i ctx 0)
           | _ -> assert false)
      in
      Boolean.mk_ite ctx is_minus minus_n n
    | (T_int.Power | T_real.RPower), [t1; t2], _ ->
      Arithmetic.mk_power ctx
        (of_term ctx env penv fenv dtenv t1)
        (of_term ctx env penv fenv dtenv t2)
    | FVar (var, _), ts, _ when Map.Poly.mem fenv var->
      Z3.FuncDecl.apply (Map.Poly.find_exn fenv var) @@
      List.map ts ~f:(of_term ctx env penv fenv dtenv)
    | FVar (var, sorts), ts, _ ->
      let sorts = List.map ~f:(of_sort ctx dtenv) sorts in
      let sargs, sret = List.take sorts (List.length sorts - 1), List.last_exn sorts in
      Expr.mk_app ctx (FuncDecl.mk_func_decl ctx (of_var ctx var) sargs sret) @@
      List.map ~f:(of_term ctx env penv fenv dtenv) ts
    | T_real_int.ToReal, [t], _ ->
      Arithmetic.Integer.mk_int2real ctx (of_term ctx env penv fenv dtenv t)
    | T_real_int.ToInt, [t], _ ->
      Arithmetic.Real.mk_real2int ctx (of_term ctx env penv fenv dtenv t)
    | T_tuple.TupleSel (sorts, i), [t], _ ->
      let sort = of_sort ctx dtenv @@ T_tuple.STuple sorts in
      Z3.FuncDecl.apply (List.nth_exn (Tuple.get_field_decls sort) i) @@
      [of_term ctx env penv fenv dtenv t]
    | T_tuple.TupleCons sorts, ts, _ ->
      let sort = of_sort ctx dtenv @@ T_tuple.STuple sorts in
      Z3.FuncDecl.apply (Tuple.get_mk_decl sort) @@
      List.map ts ~f:(of_term ctx env penv fenv dtenv)
    | T_dt.DTCons (name, _tys, dt), ts, _ ->
      (*let dt = Datatype.update_args dt tys in*)
      Z3.FuncDecl.apply (z3_cons_of dtenv dt name) @@
      List.map ts ~f:(of_term ctx env penv fenv dtenv)
    | T_dt.DTSel (name, dt, _), ts, _ ->
      Z3.FuncDecl.apply (z3_sel_of dtenv dt name) @@
      List.map ts ~f:(of_term ctx env penv fenv dtenv)
    | T_array.AStore (_si, _se), [t1; t2; t3], _ ->
      Z3Array.mk_store ctx
        (of_term ctx env penv fenv dtenv t1)
        (of_term ctx env penv fenv dtenv t2)
        (of_term ctx env penv fenv dtenv t3)
    | T_array.ASelect (_si, _se), [t1; t2], _ ->
      Z3Array.mk_select ctx
        (of_term ctx env penv fenv dtenv t1)
        (of_term ctx env penv fenv dtenv t2)
    | T_array.AConst (si, _se), [t1], _ ->
      Z3Array.mk_const_array ctx
        (of_sort ctx dtenv si)
        (of_term ctx env penv fenv dtenv t1)
    | T_string.StringConst str, [], _ ->
      Z3.FuncDecl.apply (z3_string_of ctx str) []
    | T_sequence.Epsilon, [], _ ->
      Z3.FuncDecl.apply (z3_epsilon ctx) []
    | T_sequence.Symbol str, [], _ ->
      Z3.FuncDecl.apply (z3_symbol_of ctx str) []
    | T_sequence.Concat fin, [t1; t2], _ ->
      Z3.FuncDecl.apply (z3_concat ctx fin)
        [of_term ctx env penv fenv dtenv t1;
         of_term ctx env penv fenv dtenv t2]
    | _ -> failwith @@ "[Z3interface.of_term] not supported: " ^ Term.str_of t
  else failwith @@ "[Z3interface.of_term] not supported: " ^ Term.str_of t

and
  (* from our atom to Z3 expr *)
  of_atom ctx
    (env : (Ident.tvar, Sort.t) List.Assoc.t)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (fenv : fenv)
    (dtenv : (LogicOld.Datatype.t *Z3.Sort.sort) Set.Poly.t) atom =
  Debug.print @@ lazy (sprintf "[Z3interface.of_atom] %s" @@ Atom.str_of atom);
  if Atom.is_true atom then
    find_in_cache ctx env (T_bool.mk_true ()) ~f:(fun _ -> Boolean.mk_true ctx)
  else if Atom.is_false atom then
    find_in_cache ctx env (T_bool.mk_false ()) ~f:(fun _ -> Boolean.mk_false ctx)
  else if Atom.is_psym_app atom then
    let sym, args, _ = Atom.let_psym_app atom in
    match sym, List.map ~f:(of_term ctx env penv fenv dtenv) args with
    | T_bool.Eq, [t1; t2] ->
      Boolean.mk_eq ctx t1 t2
    | T_bool.Neq, [t1; t2] ->
      Boolean.mk_not ctx @@ Boolean.mk_eq ctx t1 t2
    | (T_int.Leq | T_real.RLeq), [t1; t2] ->
      Arithmetic.mk_le ctx t1 t2
    | (T_int.Geq | T_real.RGeq), [t1; t2] ->
      Arithmetic.mk_ge ctx t1 t2
    | (T_int.Lt | T_real.RLt), [t1; t2] ->
      Arithmetic.mk_lt ctx t1 t2
    | (T_int.Gt | T_real.RGt), [t1; t2] ->
      Arithmetic.mk_gt ctx t1 t2
    | T_int.PDiv, [t1; t2] ->
      Boolean.mk_eq ctx
        (Arithmetic.Integer.mk_mod ctx t2 t1)
        (Arithmetic.Integer.mk_numeral_i ctx 0)
    | T_int.NPDiv, [t1; t2] ->
      Boolean.mk_not ctx @@
      Boolean.mk_eq ctx
        (Arithmetic.Integer.mk_mod ctx t2 t1)
        (Arithmetic.Integer.mk_numeral_i ctx 0)
    | (T_num.NLeq _ | T_num.NGeq _ | T_num.NLt _ | T_num.NGt _), [_t1; _t2] ->
      failwith @@ sprintf "[Z3interface.of_atom] polymorphic inequalities not supported: %s" @@
      Atom.str_of atom
    | T_real_int.IsInt, [t] ->
      Arithmetic.Real.mk_is_integer ctx t
    | T_tuple.IsTuple _sorts, _ts ->
      Boolean.mk_true ctx(*ToDo*)
    (*let _s = tuple_sort_of ctx dtenv sorts in
      let istuple = failwith "[Z3interface.of_atom] is_tuple not supported" in
      Z3.FuncDecl.apply istuple ts*)
    | T_tuple.NotIsTuple _sorts, _ts ->
      Boolean.mk_false ctx(*ToDo*)
    (*let _s = tuple_sort_of ctx dtenv sorts in
      let istuple = failwith "[Z3interface.of_atom] is_tuple not supported" in
      Boolean.mk_not ctx @@ Z3.FuncDecl.apply istuple ts*)
    | T_dt.IsCons (name, dt), ts ->
      Z3.FuncDecl.apply (z3_iscons_of dtenv dt name) ts
    | T_dt.NotIsCons (name, dt), ts ->
      Boolean.mk_not ctx @@
      Z3.FuncDecl.apply (z3_iscons_of dtenv dt name) ts
    | T_sequence.IsPrefix fin, [t1; t2] ->
      Z3.FuncDecl.apply (z3_is_prefix_of ctx fin) [t1; t2]
    | T_sequence.NotIsPrefix fin, [t1; t2] ->
      Boolean.mk_not ctx @@ Z3.FuncDecl.apply (z3_is_prefix_of ctx fin) [t1; t2]
    | T_sequence.InRegExp (fin, regexp), [t1] ->
      Z3.FuncDecl.apply (z3_is_in_reg_exp ctx fin regexp) [t1]
    | T_sequence.NotInRegExp (fin, regexp), [t1] ->
      Boolean.mk_not ctx @@ Z3.FuncDecl.apply (z3_is_in_reg_exp ctx fin regexp) [t1]
    | _ -> failwith @@ sprintf "[Z3interface.of_atom] %s not supported: " @@ Atom.str_of atom
  else if Atom.is_pvar_app atom then
    let pvar, _sargs, args, _ = Atom.let_pvar_app atom in
    if List.is_empty args && not @@ List.Assoc.mem ~equal:Stdlib.(=) penv pvar then
      of_var_term ctx env dtenv @@
      Term.mk_var (Ident.pvar_to_tvar pvar) T_bool.SBool
    else
      let pred =
        match List.Assoc.find ~equal:Stdlib.(=) penv pvar with
        | None ->
          failwith @@ sprintf "[Z3interface.of_atom] %s not supported: " @@
          Ident.name_of_pvar pvar
        | Some pred -> pred
      in
      Expr.mk_app ctx pred @@ List.map args ~f:(of_term ctx env penv fenv dtenv)
  else failwith @@ sprintf "[Z3interface.of_atom] %s not supported: " @@ Atom.str_of atom

let z3_fenv_of ?(init=Map.Poly.empty) ctx
    (env : (Ident.tvar, Sort.t) List.Assoc.t)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (fenv : LogicOld.FunEnv.t)
    (dtenv : (LogicOld.Datatype.t * Z3.Sort.sort) Set.Poly.t)
  =
  let z3_fenv =
    Map.Poly.fold fenv ~init ~f:(fun ~key:var ~data:(params, sret, _, _, _) acc ->
        if Map.Poly.mem acc var then acc
        else
          let func =
            Z3.FuncDecl.mk_rec_func_decl_s
              ctx
              (Ident.name_of_tvar var)
              (List.map params ~f:(fun (_, s) -> of_sort ctx dtenv s))
              (of_sort ctx dtenv sret)
          in
          Map.Poly.add_exn acc ~key:var ~data:func)
  in
  Map.Poly.iteri fenv ~f:(fun ~key:var ~data:(params, _, def, _, _) ->
      if Map.Poly.mem init var then ()
      else
        Z3.FuncDecl.add_rec_def
          ctx
          (Map.Poly.find_exn z3_fenv var)
          (List.map params ~f:(fun (v, s) ->
               of_term ctx env penv z3_fenv dtenv (Term.mk_var v s)))
          (of_term ctx env penv z3_fenv dtenv def));
  z3_fenv
let of_formula ctx
    (env : (Ident.tvar, Sort.t) List.Assoc.t)
    (penv : (Ident.pvar, FuncDecl.func_decl) List.Assoc.t)
    (fenv : fenv)
    (dtenv : (LogicOld.Datatype.t * Z3.Sort.sort) Set.Poly.t)
    phi =
  phi
  |> Normalizer.normalize_let
  (* |> Formula.elim_let *)
  |> (fun phi' ->
      Debug.print @@ lazy
        (sprintf "[z3:of_formula]\n  %s\n  %s" (Formula.str_of phi) (Formula.str_of phi'));
      phi')
  |> Formula.equivalent_sat
  |> (of_formula ctx env penv fenv dtenv)

let check_sat_z3 solver dtenv phis =
  z3_solver_add solver phis;
  match Z3.Solver.check solver [] with
  | SATISFIABLE ->
    (match z3_solver_get_model solver with
     | Some model ->
       let model = model_of dtenv model in
       (* debug_print_z3_model model; *)
       `Sat model
     | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE -> `Unsat
  | UNKNOWN ->
    (match Z3.Solver.get_reason_unknown solver with
     | "timeout" | "canceled" -> `Timeout
     | reason -> `Unknown reason)

let max_smt_z3 context dtenv hard soft =
  let optimizer = Optimize.mk_opt context in
  Optimize.add optimizer hard;
  Map.Poly.iteri soft ~f:(fun ~key ~data ->
      List.iter data ~f:(fun (expr, weight) ->
          ignore @@ Optimize.add_soft optimizer expr (string_of_int weight) (Z3.Symbol.mk_string context key)));
  match Optimize.check optimizer with
  | SATISFIABLE ->
    let open Option.Monad_infix in
    Optimize.get_model optimizer >>= fun model ->
    let num_sat =
      Map.Poly.fold soft ~init:0 ~f:(fun ~key:_ ~data sum ->
          List.fold data ~init:sum ~f:(fun sum (expr, weight) ->
              sum + (match Model.eval model expr true with
                  | None -> 0 | Some e -> if Boolean.is_true e then weight else 0)))
    in
    Some (num_sat, model_of dtenv model)
  | _ -> None

let check_opt_maximize_z3 context dtenv phis obj =
  let optimizer = Optimize.mk_opt context in
  Optimize.add optimizer phis;
  let handle = Optimize.maximize optimizer obj in
  match Optimize.check optimizer with
  | SATISFIABLE ->
    let open Option.Monad_infix in
    Optimize.get_model optimizer >>= fun model ->
    let lower = Optimize.get_lower handle |> term_of [] [] dtenv in
    let upper = Optimize.get_upper handle |> term_of [] [] dtenv in
    Some (lower, upper, model_of dtenv model)
  | _ -> None

let get_instance =
  let new_instance cfg =
    Caml_threads.Mutex.lock mutex;
    Gc.full_major ();
    let ctx = mk_context cfg in
    let solver = Z3.Solver.mk_solver ctx None in
    let goal = Z3.Goal.mk_goal ctx false false false in
    let dtenv = Set.Poly.empty in
    let fenv = Map.Poly.empty in
    Caml_threads.Mutex.unlock mutex;
    { ctx; solver; goal; dtenv; fenv; cfg }
  in
  fun (id:int option) cfg instance_pool ->
    if not enable_solver_pool then new_instance cfg
    else
      match Hashtbl.Poly.find instance_pool (id, cfg) with
      | None -> new_instance cfg
      | Some instance -> instance

let back_instance ~reset instance_pool id instance =
  if enable_solver_pool then begin
    reset instance;
    Hashtbl.Poly.set instance_pool ~key:(id, instance.cfg) ~data:instance;
  end

let check_sat =
  let cfg = [ ("model", "true"); ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  fun ?(timeout=None) ~id fenv phis ->
    let instance = get_instance id cfg instance_pool in
    let ctx, solver = instance.ctx, instance.solver in
    instance.dtenv <- (z3_dtenv_of ~init:instance.dtenv ctx @@ Formula.and_of phis);
    instance.fenv <- (z3_fenv_of ~init:instance.fenv ctx [] [] fenv instance.dtenv);
    debug_print_z3_input phis;
    let phis = List.map phis ~f:(FunEnv.defined_formula_of fenv) in
    debug_print_z3_input phis;
    let phis' = List.map phis ~f:(of_formula ctx [] [] (instance.fenv) (instance.dtenv)) in
    (match timeout with
     | None -> ()
     | Some timeout ->
       let params = Z3.Params.mk_params ctx in
       Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
       Z3.Solver.set_parameters solver params);
    check_sat_z3 solver (instance.dtenv) phis'
    |> (fun ret -> back_instance ~reset:(fun instance -> z3_solver_reset instance.solver) instance_pool id instance; ret)

(** [untrack_phis] will be poped from solver when solving finished *)
let check_sat_unsat_core_main ?(timeout=None) ?(untrack_phis=[]) solver ctx fenv dtenv pvar_clause_map =
  (match timeout with
   | None ->
     let params = Z3.Params.mk_params ctx in
     Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "model") true;
     Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "unsat_core") true;
     Z3.Solver.set_parameters solver params
   | Some timeout ->
     let params = Z3.Params.mk_params ctx in
     Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "model") true;
     Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "unsat_core") true;
     Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
     Z3.Solver.set_parameters solver params);
  Map.Poly.iteri pvar_clause_map ~f:(fun ~key:name ~data:phi ->
      if Formula.is_true phi then ()
      else begin
        Debug.print @@ lazy (sprintf "assert and track: [%s] %s" name (Formula.str_of phi));
        let phi_expr = of_formula ctx [] [] fenv dtenv phi in
        let lable =
          find_in_cache
            ~f:(fun _ -> Boolean.mk_const_s ctx name)
            ctx []
            (Term.mk_var (Tvar name) T_bool.SBool)
        in
        z3_solver_assert_and_track solver phi_expr lable
      end);
  Z3.Solver.push solver;
  Z3.Solver.add solver (List.map untrack_phis ~f:(of_formula ctx [] [] fenv dtenv));
  (fun ret -> Z3.Solver.pop solver 1; ret) @@
  match Z3.Solver.check solver [] with
  | Z3.Solver.SATISFIABLE ->
    (match z3_solver_get_model solver with
     | Some model -> `Sat (model_of dtenv model)
     | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE ->
    Debug.print @@ lazy "unsat reason:";
    let unsat_keys = List.map ~f:Z3.Expr.to_string @@ z3_solver_get_unsat_core solver in
    List.iter unsat_keys ~f:(fun unsat_key -> Debug.print @@ lazy (unsat_key));
    `Unsat unsat_keys
  | UNKNOWN ->
    (match Z3.Solver.get_reason_unknown solver with
     | "timeout" | "canceled" -> `Timeout
     | reason -> `Unknown reason)
(** [untrack_phis] will be poped from solver when solving finished *)
let check_sat_unsat_core_main ?(timeout=None) ?(untrack_phis=[]) solver ctx fenv dtenv pvar_clause_map =
  match timeout with
  | None ->
    check_sat_unsat_core_main ~timeout ~untrack_phis solver ctx fenv dtenv pvar_clause_map
  | Some tm ->
    if tm = 0 then `Timeout(* times out immediately *) else
      Timer.enable_timeout (tm / 1000) Fn.id ignore
        (fun () -> check_sat_unsat_core_main ~timeout ~untrack_phis solver ctx fenv dtenv pvar_clause_map)
        (fun _ res -> res)
        (fun _ -> function Timer.Timeout -> `Timeout | e -> raise e)

let check_sat_unsat_core ?(timeout=None) fenv pvar_clause_map =
  let ctx =
    let cfg = [ ("model", "true"); ("unsat_core", "true") ] in
    let cfg = if validate then cfg @ validate_cfg else cfg in
    let cfg =
      match timeout with
      | None -> cfg
      | Some timeout -> cfg @ [("timeout", string_of_int timeout)]
    in
    mk_context cfg
  in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of @@ snd @@ List.unzip @@ Map.Poly.to_alist pvar_clause_map in
  let solver = Z3.Solver.mk_solver ctx None in
  let fenv = z3_fenv_of ctx [] [] fenv dtenv in
  (match timeout with
   | None -> ()
   | Some timeout ->
     let params = Z3.Params.mk_params ctx in
     Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
     Z3.Solver.set_parameters solver params);
  check_sat_unsat_core_main ~timeout solver ctx fenv dtenv pvar_clause_map

let max_smt fenv hard soft =
  let cfg = [
    ("MODEL", "true");
    (* ("well_sorted_check", "true"); *)
  ] in
  let ctx = mk_context cfg in
  let soft_phi = Map.Poly.to_alist soft |> List.unzip |> snd |> List.join |> List.unzip |> fst |> Formula.and_of in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of (soft_phi::hard) in
  let hard = List.map hard ~f:(of_formula ctx [] [] fenv dtenv) in
  let soft = Map.Poly.map soft ~f:(List.map ~f:(fun (phi, weight) -> of_formula ctx [] [] fenv dtenv phi , weight)) in
  max_smt_z3 ctx dtenv hard soft
(** ToDo: use MaxSMT instead *)
let max_smt_of ~id fenv num_ex phis =
  let cfg = [("unsat_core", "true")] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  instance.dtenv <- z3_dtenv_of ~init:instance.dtenv ctx @@ Formula.and_of phis;
  instance.fenv <- (z3_fenv_of ~init:(instance.fenv) ctx [] [] fenv instance.dtenv);
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let solver = instance.solver in
  let name_map0 =
    List.map phis ~f:(of_formula ctx [] [] fenv dtenv)
    |> List.foldi ~init:Map.Poly.empty ~f:(fun i map phi ->
        let name = "#S_" ^ (string_of_int i) in
        let lable =
          find_in_cache
            ~f:(fun _ -> Boolean.mk_const_s ctx name)
            ctx []
            (Term.mk_var (Tvar name) T_bool.SBool)
        in
        Map.Poly.update map lable ~f:(function None -> phi | Some x -> x)) in
  let rec inner num_ex models ignored name_map =
    if num_ex <= 0 then models
    else begin
      Map.Poly.iteri name_map ~f:(fun ~key ~data -> z3_solver_assert_and_track solver data key);
      z3_solver_reset solver;
      match Z3.Solver.check solver [] with
      | Z3.Solver.SATISFIABLE ->
        (match z3_solver_get_model solver with
         | None -> assert false
         | Some model ->
           let models' = Set.Poly.add models (model_of dtenv model) in
           let name_map' = Map.Poly.filter_keys ~f:(Set.Poly.mem ignored) name_map0 in
           inner (num_ex - 1) models' Set.Poly.empty name_map')
      | UNSATISFIABLE ->
        let ucore = List.hd_exn @@ z3_solver_get_unsat_core solver in
        inner num_ex models (Set.Poly.add ignored ucore) (Map.Poly.remove name_map ucore)
      | UNKNOWN -> assert false
    end
  in
  inner num_ex Set.Poly.empty Set.Poly.empty name_map0
  |> (fun ret ->
      back_instance ~reset:(fun ins -> z3_solver_reset ins.solver) instance_pool id instance;
      ret)

let check_opt_maximize fenv phis obj =
  let cfg = [ ("model", "true") ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  let ctx = mk_context cfg in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of phis in
  let z3fenv = z3_fenv_of ctx [] [] fenv dtenv in
  debug_print_z3_input phis;
  let phis = List.map phis ~f:(of_formula ctx [] [] z3fenv dtenv) in
  let obj = of_term ctx [] [] (z3_fenv_of ctx [] [] fenv dtenv) dtenv obj in
  check_opt_maximize_z3 ctx dtenv phis obj

let check_valid ~id fenv phi =
  match check_sat ~id fenv [Formula.negate phi] with
  | `Unsat -> `Valid
  | `Sat model -> `Invalid model
  | res -> res

let is_valid ~id fenv phi = match check_valid ~id fenv phi with `Valid -> true | _ -> false
exception Unknown
let is_valid_exn ~id fenv phi = match check_valid ~id fenv phi with `Valid -> true | `Invalid _ -> false | _ -> raise Unknown
let is_sat ~id fenv phi = match check_sat ~id fenv [phi] with `Sat _ -> true | _ -> false

(** assume that [phi] is alpha-renamed *)
let z3_simplify ~id fenv phi =
  let cfg = [("model", "true");] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  instance.dtenv <- (z3_dtenv_of ~init:(instance.dtenv) ctx phi);
  instance.fenv <- (z3_fenv_of ~init:(instance.fenv) ctx [] [] fenv instance.dtenv);
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let symplify_params = Z3.Params.mk_params @@ ctx in
  let penv = penv_of phi ctx dtenv in
  let lenv = Map.Poly.to_alist @@ Formula.let_sort_env_of phi in
  let tenv = lenv @ (Formula.term_sort_env_of phi |> Set.Poly.to_list) in
  Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "elim_ite") true;
  Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "push_ite_arith") true;
  let rec inner = function
    | Formula.LetFormula (v, sort, def, body, info) ->
      let def' =
        if Stdlib.(sort = T_bool.SBool) then
          T_bool.of_formula @@ inner @@ Formula.of_bool_term def
        else def
      in
      Formula.LetFormula (v, sort, def', inner body, info)
    | phi ->
      phi
      (* |> (fun phi -> print_endline @@ Formula.str_of phi ^ "\n"; phi) *)
      |> of_formula ctx tenv penv fenv dtenv
      |> (fun phi -> Z3.Expr.simplify phi @@ Some symplify_params)
      |> formula_of (List.rev tenv) penv dtenv
      |> Evaluator.simplify
      (* |> (fun phi -> print_endline @@ Formula.str_of phi ^ "\n"; phi) *)
  in
  let ret = inner phi in
  back_instance ~reset:ignore instance_pool id instance;
  ret

let qelim ~id fenv phi =
  if Formula.is_bind phi then
    let _ = Debug.print @@ lazy (sprintf "[Z3interface.qelim] %s" (Formula.str_of phi)) in
    let cfg = [ ("model", "true"); ] in
    let instance = get_instance id cfg instance_pool in
    let ctx = instance.ctx in
    let goal = instance.goal in
    instance.dtenv <- z3_dtenv_of ~init:instance.dtenv ctx phi;
    instance.fenv <- z3_fenv_of ~init:instance.fenv ctx [] [] fenv instance.dtenv;
    let symplify_params = Z3.Params.mk_params ctx in
    let penv = penv_of phi ctx instance.dtenv in
    Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "elim_ite") true;
    let qe_params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool qe_params (Z3.Symbol.mk_string ctx "eliminate_variables_as_block") true;
    z3_goal_add goal [of_formula ctx [] penv instance.fenv instance.dtenv phi];
    let g =
      Goal.as_expr @@
      Z3.Tactic.ApplyResult.get_subgoal (Z3.Tactic.apply (Z3.Tactic.mk_tactic ctx "qe") goal (Some qe_params)) 0
    in
    let expr = Z3.Expr.simplify g (Some symplify_params) in
    let _ = Debug.print @@ lazy ("quantifier eliminated: " ^ Z3.Expr.to_string expr) in
    let phi =
      Evaluator.simplify @@ Formula.nnf_of @@
      formula_of [] penv instance.dtenv expr
    in
    back_instance ~reset:(fun ins -> Goal.reset ins.goal) instance_pool id instance;
    (* print_endline @@ "qelim ret: " ^ Formula.str_of phi; *)
    phi
  else phi

let smtlib2_str_of_formula ctx fenv dtenv phi =
  Expr.to_string @@
  of_formula ctx
    (Set.Poly.to_list @@ Formula.term_sort_env_of phi)
    (penv_of phi ctx dtenv) fenv dtenv
    phi

let expr_cache:(context, (Formula.t, Z3.Expr.expr) Hashtbl.Poly.t) Hashtbl.Poly.t = Hashtbl.Poly.create ()
let find_in_expr_cache ctx phi ~f =
  let cache = Hashtbl.Poly.find_or_add expr_cache ctx ~default:(fun _ -> Hashtbl.Poly.create ()) in
  Hashtbl.Poly.find_or_add cache phi ~default:(fun _ -> f ())
let expr_of ctx fenv dtenv phi =
  find_in_expr_cache ctx phi ~f:(fun _ ->
      try of_formula ctx [] [] fenv dtenv @@ Evaluator.simplify phi
      with _ -> of_formula ctx [] [] fenv dtenv @@ Formula.mk_true ())
let str_of_asserts_of_solver solver =
  "Asserts of solver:" ^
  String.concat_map_list ~sep:"\n\t" ~f:Expr.to_string @@ Z3.Solver.get_assertions solver
let check_valid_inc solver phis =
  match Z3.Solver.check solver phis with
  | SATISFIABLE ->
    (* Debug.print @@ lazy (sprintf "%s \n check valid -> (sat)invalid" (str_of_asserts_of_solver solver)); *)
    false
  | _ ->
    (* Debug.print @@ lazy (sprintf "%s \n checksat valid -> (unsat)valid" (str_of_asserts_of_solver solver)); *)
    true
let star and_flag = function
  | Formula.Atom (a, _) when Atom.is_pvar_app a -> None
  | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _) when Atom.is_pvar_app a -> None
  | phi -> Some (Evaluator.simplify @@ if and_flag then phi else Formula.negate phi)
let rec simplify_term solver ctx fenv dtenv = function
  | Term.FunApp (T_bool.Formula phi, [], info) ->
    let phi, has_changed = simplify_formula solver ctx fenv dtenv phi in
    T_bool.of_formula ~info phi, has_changed
  | Term.FunApp (T_bool.IfThenElse, [t1; t2; t3], info) ->
    let t1, has_changed1 = simplify_term solver ctx fenv dtenv t1 in
    let t2, has_changed2 = (*ToDo: add t1 to the context*)simplify_term solver ctx fenv dtenv t2 in
    let t3, has_changed3 = (*ToDo: add not t1 to the context*)simplify_term solver ctx fenv dtenv t3 in
    T_bool.mk_if_then_else ~info t1 t2 t3, has_changed1 || has_changed2 || has_changed3
  | t -> t, false
and simplify_atom solver ctx fenv (dtenv:dtenv) atom =
  if Atom.is_pvar_app atom then
    let pvar, sorts, args, info = Atom.let_pvar_app atom in
    let args', _has_changed_list =
      List.unzip @@ List.map ~f:(simplify_term solver ctx fenv dtenv) args
    in
    Atom.mk_pvar_app pvar sorts args' ~info,
    false(*List.exists ~f:ident has_changed_list*)
  else
    let phi = Formula.mk_atom atom in
    (* Debug.print @@ lazy (sprintf "simplify atom: %s" (Formula.str_of phi)); *)
    if check_valid_inc solver [expr_of ctx fenv dtenv @@ Formula.negate phi] then
      Atom.mk_true (), true
    else if check_valid_inc solver [expr_of ctx fenv dtenv @@ phi] then
      Atom.mk_false (), true
    else atom, false
and check_sub_formulas solver ctx fenv (dtenv:dtenv) and_flag phi =
  let cs = Set.Poly.to_list @@ if and_flag then Formula.conjuncts_of phi else Formula.disjuncts_of phi in
  (* Debug.print @@ lazy (sprintf "Cs: %s" (String.concat_map_list ~sep:"\n\t" cs ~f:Formula.str_of)); *)
  (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
  Z3.Solver.push solver;
  let cs', _ , has_changed =
    List.fold_left cs ~init:([], List.tl_exn cs, false)
      ~f:(fun (cs', cs, has_changed) c ->
          (* Debug.print @@ lazy (sprintf "c: %s" (Formula.str_of c)); *)
          Z3.Solver.push solver;
          let exprs =
            List.map ~f:(expr_of ctx fenv dtenv) @@
            List.filter_map cs ~f:(star and_flag)
          in
          z3_solver_add solver exprs;
          (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
          let c', has_changed' = simplify_formula solver ctx fenv dtenv c in
          Z3.Solver.pop solver 1;
          (* Debug.print @@ lazy (sprintf "c': %s" (Formula.str_of c')); *)
          (match star and_flag c' with
           | Some phi -> z3_solver_add solver [expr_of ctx fenv dtenv phi] | None -> ());
          (c' :: cs'), (match cs with | _::tl -> tl | _ -> []),
          has_changed || has_changed') in
  Z3.Solver.pop solver 1;
  let cs' = List.rev cs' in
  (* Debug.print @@ lazy (sprintf "compare Cs to Cs':\nCs :%s" (String.concat_map_list ~sep:"\n\t" cs ~f:Formula.str_of)); *)
  (* Debug.print @@ lazy (sprintf "Cs': %s" (String.concat_map_list ~sep:"\n\t" cs' ~f:Formula.str_of)); *)
  let ret = Evaluator.simplify @@ if and_flag then Formula.and_of cs' else Formula.or_of cs' in
  if has_changed then begin
    (* Debug.print @@ lazy ("has changed."); *)
    fst @@ check_sub_formulas solver ctx fenv dtenv and_flag ret, true
  end else ret, false
and simplify_formula solver ctx fenv (dtenv:dtenv) phi =
  (* Debug.print @@ lazy (sprintf "[Z3interface.simplify_formula] %s" (Formula.str_of phi) ); *)
  (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
  match phi with
  | Formula.Atom (atom, _) when not (Atom.is_true atom || Atom.is_false atom) ->
    let atom, has_changed = simplify_atom solver ctx fenv dtenv atom in
    Formula.mk_atom atom, has_changed
  | Formula.UnaryOp (Not, Atom (atom, _), _)
    when not (Atom.is_true atom || Atom.is_false atom) ->
    let atom, has_changed = simplify_atom solver ctx fenv dtenv atom in
    Formula.negate (Formula.mk_atom atom), has_changed
  | Formula.BinaryOp (And, _, _, _) -> check_sub_formulas solver ctx fenv dtenv true phi
  | Formula.BinaryOp (Or, _, _, _) -> check_sub_formulas solver ctx fenv dtenv false phi
  | Formula.LetFormula (var, sort, def, body, info) ->
    let def, _ = simplify_term solver ctx fenv dtenv def in
    let body, has_changed = simplify_formula solver ctx fenv dtenv body in
    Formula.LetFormula (var, sort, def, body, info), has_changed
  | _ -> phi, false
and simplify ?(timeout=None) ~id fenv phi =
  Debug.print @@ lazy ("===========simplify start=============");
  Debug.print @@ lazy (sprintf "the formula:\n  %s" @@ Formula.str_of phi);
  let cfg = ["model", "true"] in
  let instance = get_instance id cfg instance_pool in
  let ctx, solver = instance.ctx, instance.solver in
  instance.dtenv <- (z3_dtenv_of ~init:(instance.dtenv) ctx phi);
  instance.fenv <- (z3_fenv_of ~init:(instance.fenv) ctx [] [] fenv instance.dtenv);
  (* Debug.print @@ lazy (sprintf "the smtlib2 formua:\n\t%s" @@ smtlib2_str_of_formula ctx dtenv phi); *)
  (* let solver = Z3.Solver.mk_solver ctx None in *)
  (match timeout with
   | None -> ()
   | Some timeout ->
     let params = Z3.Params.mk_params ctx in
     Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
     Z3.Solver.set_parameters solver params);
  let phi = Normalizer.normalize_let phi in
  let ret =
    z3_simplify ~id fenv @@
    fst @@ simplify_formula solver ctx instance.fenv instance.dtenv @@
    z3_simplify ~id fenv @@
    Formula.nnf_of phi
  in
  Debug.print @@ lazy (sprintf "result:\n  %s\n===========simplify end=============" @@ Formula.str_of ret);
  back_instance ~reset:(fun instance -> z3_solver_reset instance.solver) instance_pool id instance;
  ret
let of_formula_with_z3fenv = of_formula

let of_formula ctx env penv fenv dtenv phi = (** For external calls *)
  of_formula ctx env penv (z3_fenv_of ctx env penv fenv dtenv) dtenv phi
