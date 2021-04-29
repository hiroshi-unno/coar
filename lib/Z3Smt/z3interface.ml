open Core
open Z3
open Common
open Common.Util
open Ast
open Ast.LogicOld

let validate = false
let validate_cfg = [ ("model_validate", "true"); ("well_sorted_check", "true") ]

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))
(* let _ = Z3.set_global_param "smt.macro_finder" "true" *)
let debug_print_z3_input phis =
  Debug.print @@ lazy "Z3 input formulas :";
  List.iter phis ~f:(fun phi -> Debug.print @@ lazy (Formula.str_of phi))
let debug_print_z3_model model =
  Debug.print @@ lazy ("Z3 output model :" ^ TermSubst.str_of_model model)

type dtenv = (LogicOld.Datatype.t * Z3.Sort.sort) Set.Poly.t
type fenv = (Ident.tvar * (Ident.tvar * LogicOld.Sort.t) list * LogicOld.Sort.t * LogicOld.Term.t * (LogicOld.Formula.t Set.Poly.t)) Set.Poly.t

(** decoding *)

(* let rec sort_of s = match Z3.Sort.get_sort_kind s with
   | Z3enums.BOOL_SORT -> T_bool.SBool
   | Z3enums.INT_SORT -> T_int.SInt
   | Z3enums.REAL_SORT -> T_real.SReal
   | Z3enums.UNINTERPRETED_SORT -> 
   let name = Symbol.get_string @@ Z3.Sort.get_name s in
   T_dt.SUS (name, [])
   | Z3enums.ARRAY_SORT ->
   let zi = Z3Array.get_domain s in
   let ze = Z3Array.get_range s in
   T_array.SArray (sort_of zi, sort_of ze)
   | _ -> assert false (* TODO: implement others *)
*)
let rec sort_of env s = 
  match Z3.Sort.get_sort_kind s with
  | Z3enums.BOOL_SORT -> T_bool.SBool
  | Z3enums.INT_SORT -> T_int.SInt
  | Z3enums.REAL_SORT -> T_real.SReal
  | Z3enums.UNINTERPRETED_SORT -> 
    let name = Symbol.get_string @@ Z3.Sort.get_name s in
    T_dt.SUS (name, [])
  | Z3enums.ARRAY_SORT ->
    let zi = Z3Array.get_domain s in
    let ze = Z3Array.get_range s in
    T_array.SArray (sort_of env zi , sort_of env ze)
  | Z3enums.DATATYPE_SORT ->
    begin match Set.Poly.find env ~f:(
        fun (_, sort) -> Stdlib.(=) s sort
      ) with
    | Some (dt, _) -> LogicOld.T_dt.SDT(dt)
    | _ -> assert false
    end
  | _ -> assert false (* TODO: implement others *)


let func_name_of_full name =
  List.hd_exn @@ String.split name ~on:'_'

let is_iscons name =
  String.split name ~on:'_'
  |> List.rev
  |> List.hd_exn 
  |> Stdlib.(=) "is"

let look_up_func_of_dt dt sort func =
  (* Debug.print @@ lazy (sprintf "look_up_func:%d :%s" (Z3.FuncDecl.get_id func) (Z3.FuncDecl.to_string func)); *)
  let id = Z3.FuncDecl.get_id func in
  let conses = Datatype.conses_of dt in
  let z3_conses = Z3.Datatype.get_constructors sort in
  let z3_testers = Z3.Datatype.get_recognizers sort in
  let z3_selss = Z3.Datatype.get_accessors sort in
  let z3_funcs = List.zip3_exn z3_conses z3_testers z3_selss in
  List.fold2_exn conses z3_funcs ~init:`Unkonwn ~f:(
    fun ret cons (z3_cons, z3_tester, z3_sels) ->
      match ret with
      |`Unkonwn ->
        if id = FuncDecl.get_id z3_cons then `Cons (cons)
        else if id = FuncDecl.get_id z3_tester then `IsCons(cons)
        else List.fold2_exn (LogicOld.Datatype.sels_of_cons cons) z3_sels ~init:ret ~f:(
            fun ret sel z3_sel -> 
              (* Debug.print @@ lazy (sprintf "search_sel %d =? %d :%s" id (Z3.FuncDecl.get_id z3_sel) (Z3.FuncDecl.to_string z3_sel)); *)
              match ret with
              | `Unkonwn -> if id = (FuncDecl.get_id z3_sel) then `Sel(sel) else ret
              | _ -> ret
          )
      | _ -> ret
  )
let look_up_func dtenv func =
  Set.Poly.find_map dtenv ~f:(
    fun (dt, sort) -> 
      match look_up_func_of_dt dt sort func with
      | `Unkonwn -> None
      | ret -> Some (dt, ret)
  ) 

let rec parse_term = function
  | Sexp.Atom "x" -> Term.mk_var (Ident.Tvar("x")) T_real.SReal
  | Sexp.Atom ident -> begin
      try
        T_int.mk_int (Z.of_string ident)
      with _ -> begin
          try
            T_real.mk_real (Q.of_string ident)
          with _ -> assert false
        end
    end
  | Sexp.List [Sexp.Atom "-"; t] ->
    let t = parse_term t in
    T_int.mk_neg(*ToDo*) t
  | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
    let arg = parse_term arg in
    List.fold args ~init:arg ~f:(fun acc t -> T_int.mk_add(*ToDo*) acc (parse_term t))
  | Sexp.List (Sexp.Atom "*" :: arg :: args) ->
    let arg = parse_term arg in
    List.fold args ~init:arg ~f:(fun acc t -> T_int.mk_mult(*ToDo*) acc (parse_term t))
  | Sexp.List [Sexp.Atom "^"; t1; t2] ->
    let t1 = parse_term t1 in
    let t2 = parse_term t2 in
    T_int.mk_power(*ToDo*) t1 t2
  | _ -> assert false
let parse_root_obj e =
  match e with
  | Sexp.List [Sexp.Atom "root-obj"; t; n] ->
    let t = parse_term t in t, (int_of_string @@ Sexp.to_string n)
  | _ -> failwith ((Sexp.to_string e) ^ " is not root-obj")

let var_of s = Scanf.unescaped @@ (try Scanf.sscanf s "|%s@|" ident with _ -> s)

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
(* term_of: (Ident.tvar, Sort.t) Env.t -> (Ident.pvar, FuncDecl.func_decl) Env.t -> Z3.Expr.expr -> info Logic.term *)
and term_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) (dtenv:dtenv) expr = (*try*)
  (* Debug.print @@ lazy ("term of z3:" ^ Z3.Expr.to_string expr); *)
  if Boolean.is_true expr then T_bool.of_atom (Atom.mk_true ())
  else if Boolean.is_false expr then T_bool.of_atom (Atom.mk_false ())
  else if Boolean.is_ite expr then
    match Expr.get_args expr with
    | e1::e2::[e3] -> T_bool.ifte (formula_of senv penv dtenv e1) (term_of senv penv dtenv e2) (term_of senv penv dtenv e3)
    | _ -> assert false
  else if Arithmetic.is_int_numeral expr then T_int.mk_int (Arithmetic.Integer.get_big_int expr)
  else if Arithmetic.is_rat_numeral expr then T_real.mk_real (Arithmetic.Real.get_ratio expr)
  else if Arithmetic.is_algebraic_number expr then
    let expr = Sexp.of_string @@ Expr.to_string expr in
    let t, n = parse_root_obj expr in
    T_real.mk_alge t n
  else if Arithmetic.is_add expr then
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_int.SInt -> apply senv penv dtenv T_int.mk_add expr
    | T_real.SReal -> apply senv penv dtenv T_real.mk_radd expr
    | _ -> failwith (Z3.Sort.to_string @@ Expr.get_sort expr)
  else if Arithmetic.is_sub expr then
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_int.SInt -> apply senv penv dtenv T_int.mk_sub expr
    | T_real.SReal -> apply senv penv dtenv T_real.mk_rsub expr
    | _ -> failwith (Z3.Sort.to_string @@ Expr.get_sort expr)
  else if Arithmetic.is_mul expr then
    match sort_of dtenv @@ Expr.get_sort expr with
    | T_int.SInt -> apply senv penv dtenv T_int.mk_mult expr
    | T_real.SReal -> apply senv penv dtenv T_real.mk_rmult expr
    | _ -> failwith (Z3.Sort.to_string @@ Expr.get_sort expr)
  else if Arithmetic.is_idiv expr then apply_bop senv penv dtenv T_int.mk_div expr
  else if Arithmetic.is_div expr then apply_bop senv penv dtenv T_real.mk_rdiv expr
  else if Arithmetic.is_modulus expr then apply_bop senv penv dtenv T_int.mk_mod expr
  else if Arithmetic.is_remainder expr then apply_bop senv penv dtenv T_int.mk_rem expr
  else if AST.is_var @@ Expr.ast_of_expr expr then
    let var = Expr.to_string expr in
    (* Debug.print @@ lazy ("z3 var :" ^ (Expr.to_string expr)); *)
    let index = Env.length senv - Scanf.sscanf var "(:var %d)" ident - 1 in
    let (var, sort) = Env.nth senv index in
    Term.mk_var var sort
  else if Expr.is_const expr then
    let var = Ident.Tvar (var_of @@ Expr.to_string expr) in
    let sort = (sort_of dtenv @@ Expr.get_sort expr) in
    match sort with
    | T_dt.SDT (_) -> dt_term_of senv penv dtenv expr
    | _ -> 
      (* Debug.print @@ lazy ("z3 const var :" ^ (Expr.to_string expr)); *)
      Term.mk_var var sort
  else if Z3Array.is_store expr then
    let args = Expr.get_args expr in
    let targs = List.map args ~f:(term_of senv penv dtenv) in
    match targs with
    | t1::t2::t3::_ -> T_array.mk_store t1 t2 t3
    | _ -> assert false
  else if Z3Array.is_constant_array expr then
    let sa = sort_of dtenv @@ Expr.get_sort expr in
    let targs = List.map ~f:(term_of senv penv dtenv) @@ Expr.get_args expr in
    match targs with
    | t1::_ -> T_array.mk_const_array sa t1
    | _ -> assert false
  else if Z3Array.is_select expr then
    let args = Expr.get_args expr in
    let targs = List.map args ~f:(term_of senv penv dtenv) in
    match targs with
    | [t1; t2] ->
      begin match T_array.eval_select t1 t2 with
        | Some te -> te
        | _ -> T_array.mk_select t1 t2
      end
    | _ -> assert false
  else
    dt_term_of senv penv dtenv expr
and
  (* from Z3 expr to our atom *)
  (* atom_of: (Ident.tvar, Sort.t) Env.t -> (Ident.pvar, FuncDecl.func_decl) Env.t -> Z3.Expr.expr -> info Logic.Atom.t *)
  atom_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) (dtenv:dtenv) expr =
  (* Debug.print @@ lazy ("atom of z3:" ^ Z3.Expr.to_string expr); *)
  if Boolean.is_true expr then Atom.mk_true ()
  else if Boolean.is_false expr then Atom.mk_false ()
  else if Boolean.is_eq expr then apply_brel senv penv dtenv T_bool.mk_eq expr
  else if Arithmetic.is_le expr then apply_brel senv penv dtenv T_int.mk_leq expr
  else if Arithmetic.is_ge expr then apply_brel senv penv dtenv T_int.mk_geq expr
  else if Arithmetic.is_lt expr then apply_brel senv penv dtenv T_int.mk_lt expr
  else if Arithmetic.is_gt expr then apply_brel senv penv dtenv T_int.mk_gt expr
  else if AST.is_var @@ Expr.ast_of_expr expr then
    let var = Expr.to_string expr in
    let index = Env.length senv - Scanf.sscanf var "(:var %d)" (fun x -> x) - 1 in
    let (Ident.Tvar var, _sort(* assume bool*)) = Env.nth senv index in
    Atom.mk_pvar_app (Ident.Pvar var) [] []
  else if Expr.is_const expr then
    Atom.mk_pvar_app (Ident.Pvar (var_of @@ Expr.to_string expr)) [] []
  else failwith ("atom_of_z3:" ^Z3.Expr.to_string expr) (* ToDo: implement others *)
and
  (* from Z3 expr to our formula *)
  (* formula_of: (Ident.tvar, Sort.t) Env.t -> (Ident.pvar, FuncDecl.func_decl) Env.t -> Z3.Expr.expr -> info Logic.Formula.t *)
  formula_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) (dtenv:dtenv) expr =
  (* Debug.print @@ lazy ("formula of z3:" ^ Z3.Expr.to_string expr); *)
  if Boolean.is_not expr then
    match Expr.get_args expr with
    | [body] -> Formula.mk_neg (formula_of senv penv dtenv body)
    | _ -> assert false
  else if Boolean.is_and expr then
    Expr.get_args expr |> List.map ~f:(formula_of senv penv dtenv) |> Formula.and_of
  else if Boolean.is_or expr then
    Expr.get_args expr |> List.map ~f:(formula_of senv penv dtenv) |> Formula.or_of
  else if Boolean.is_iff expr then
    Expr.get_args expr
    |> List.map ~f:(formula_of senv penv dtenv)
    |> function [phi1; phi2] -> Formula.mk_iff phi1 phi2 | _ -> assert false
  else if Boolean.is_implies expr then
    Expr.get_args expr
    |> List.map ~f:(formula_of senv penv dtenv)
    |> function [phi1; phi2] -> Formula.mk_imply phi1 phi2 | _ -> assert false
  else if Boolean.is_ite expr then
    match Expr.get_args expr with
    | e1::e2::[e3] -> Formula.of_bool_term @@ T_bool.ifte (formula_of senv penv dtenv e1) (term_of senv penv dtenv e2) (term_of senv penv dtenv e3)
    | _ -> assert false
  else if AST.is_quantifier @@ Expr.ast_of_expr expr then
    let q = Quantifier.quantifier_of_expr expr in
    let binder = if Quantifier.is_universal q then Formula.Forall else Formula.Exists in
    let bounds = (* Option.unwrap @@ *) List.zip_exn (* The type of core.List.zip is changed in the latest core library *)
        (Quantifier.get_bound_variable_names q
         |> List.map ~f:(fun x -> Ident.Tvar (Symbol.get_string x)))
        (Quantifier.get_bound_variable_sorts q
         |> List.map ~f:(sort_of dtenv)) in
    let senv = Env.update bounds senv in
    let body = Quantifier.get_body q |> formula_of senv penv dtenv in
    Formula.mk_bind binder (SortEnv.of_list bounds) body
  else Formula.mk_atom (atom_of senv penv dtenv expr)
and dt_term_of (senv: (Ident.tvar, Sort.t) Env.t) (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) (dtenv:dtenv) expr =
  let func = Z3.Expr.get_func_decl expr in
  let ts = Z3.Expr.get_args expr in
  let sort = sort_of dtenv @@ FuncDecl.get_range func in
  let name = Symbol.to_string @@ FuncDecl.get_name func in
  begin match look_up_func dtenv func with
    | Some (dt, `Cons(cons)) -> T_dt.mk_cons dt (Datatype.name_of_cons cons) @@ List.map ts ~f:(term_of senv penv dtenv)
    | Some (dt, `IsCons(cons)) -> T_bool.of_atom @@ T_dt.mk_is_cons dt cons @@ term_of senv penv dtenv @@ List.hd_exn ts
    | Some (dt, `Sel(sel)) -> T_dt.mk_sel dt (Datatype.name_of_sel sel) @@ term_of senv penv dtenv @@ List.hd_exn ts
    | None when T_dt.is_sdt sort -> Term.mk_var (Ident.Tvar(name)) sort
    | _ -> T_bool.of_formula (formula_of senv penv dtenv expr)
  end

let dummy_term_map_of terms =
  Set.Poly.filter terms ~f:(function |(_, T_dt.SUS _) -> true | _ -> false) 
  |> Set.Poly.map ~f:(
    fun (tvar, sort) -> (tvar, mk_fresh_dummy_term sort))
  |> Set.Poly.to_list 
  |> Map.Poly.of_alist_exn

let add_dummy_term model =
  let terms = List.filter_map model ~f:(
      function |_, Some(t) -> Some(t) |_ -> None
    ) in
  List.fold_left terms ~init:Set.Poly.empty ~f:(
    fun ret term -> 
      Set.Poly.filter ~f:(function |(_, T_dt.SUS _) -> true | _ -> false) @@
      Set.Poly.union ret @@ Term.term_sort_env_of term 
  ) |>
  Set.Poly.iter ~f:(
    fun (tvar, sort) -> add_dummy_term tvar sort
  )


let model_of dtenv model =
  let decls = Model.get_decls model in
  let model = List.map decls ~f:(fun decl ->
      let x = Symbol.get_string (FuncDecl.get_name decl) in
      let s = Sort.mk_fun @@ List.map ~f:(sort_of dtenv) @@ FuncDecl.get_domain decl @ [FuncDecl.get_range decl] in
      if FuncDecl.get_arity decl = 0 then
        match Model.get_const_interp model decl with
        | Some expr ->
          let t = term_of Env.empty Env.empty dtenv expr in
          (Ident.Tvar x, s), Some t
        | None -> (Ident.Tvar x, s), None
      else
        match Model.get_func_interp model decl with
        | Some _func(*ToDo*) -> (Ident.Tvar x, s), None
        | None -> (Ident.Tvar x, s), None)
  in 
  Debug.print @@ lazy ("model is :" ^ LogicOld.TermSubst.str_of_model model);
  model

(*let model_of model =
  let open Core in
  let decls = Model.get_const_decls model in
  let open Option.Monad_infix in
  List.map decls ~f:(fun decl ->
   (Ident.Tvar (Symbol.get_string (FuncDecl.get_name decl)),
    Model.get_const_interp model decl >>= fun expr ->
    Some(term_of Env.empty Env.empty expr)))*)

(** encoding *)

let of_var ctx (Ident.Tvar var) =
  var |> String.escaped |> Symbol.mk_string ctx

let list_type s ctx = Z3List.mk_sort ctx (Symbol.mk_string ctx "list") s
let array_type t1 t2 ctx = Z3Array.mk_sort ctx t1 t2
let tuple_type sorts ctx =
  let num = List.length sorts in
  Tuple.mk_sort ctx
    ("tuple" ^ string_of_int num |> Symbol.mk_string ctx)
    (List.init num
       ~f:(fun i -> "get_" ^ Ordinal.string_of @@ Ordinal.make i |> Symbol.mk_string ctx))
    sorts
let sorts_of_tuple sort =
  sort
  |> Tuple.get_mk_decl
  |> FuncDecl.get_domain

(* from our sort to Z3 sort *)
(* let rec of_sort ctx = function
   | T_int.SInt -> Arithmetic.Integer.mk_sort ctx
   | T_real.SReal -> Arithmetic.Real.mk_sort ctx
   | T_bool.SBool -> Boolean.mk_sort ctx
   | T_dt.SUS (name, []) -> Z3.Sort.mk_uninterpreted_s ctx name
   | T_array.SArray (si, se) -> Z3Array.mk_sort ctx (of_sort ctx si) (of_sort ctx se)
   | _ -> assert false *)

let rec of_sort ctx env = function
  | T_int.SInt -> Arithmetic.Integer.mk_sort ctx
  | T_real.SReal -> Arithmetic.Real.mk_sort ctx
  | T_bool.SBool -> Boolean.mk_sort ctx
  | T_dt.SUS (name, []) -> Z3.Sort.mk_uninterpreted_s ctx name
  | T_array.SArray (si, se) -> Z3Array.mk_sort ctx (of_sort ctx env si) (of_sort ctx env se)
  | T_dt.SDT(dt) -> 
    begin match Set.Poly.find env ~f:(
        fun (dt1, _) -> Stdlib.(=) (LogicOld.Datatype.full_name_of dt1) (LogicOld.Datatype.full_name_of dt)
      ) with
    | Some (_, sort) -> sort
    | None -> failwith ("unkonwn adt sort:" ^ (LogicOld.Datatype.str_of dt))
    end
  | sort -> failwith ("unkonwn adt sort:" ^ (LogicOld.Term.str_of_sort sort))

let str_of_z3_env env =
  Set.Poly.fold env ~init:"z3_env:" ~f:(
    fun ret (dt, sort) ->
      ret ^ "\nLogicOld:\n" ^ (LogicOld.Datatype.str_of dt) ^ "Z3:\n" ^ (Z3.Sort.to_string sort) ^
      List.fold2_exn (Z3.Datatype.get_constructors sort) (Z3.Datatype.get_accessors sort) ~init:"" ~f:(
        fun ret cons sels ->
          ret ^ sprintf "\n|%d: %s" (Z3.FuncDecl.get_id cons) (Z3.FuncDecl.to_string cons) ^ 
          List.fold_left sels ~init:("") ~f:(
            fun ret sel -> ret ^ "\n>>> " ^ (sprintf "%d: %s" (Z3.FuncDecl.get_id sel) (Z3.FuncDecl.to_string sel))
          )
      ) ^
      List.fold_left (Z3.Datatype.get_recognizers sort) ~init:"\ntesters:" ~f:(
        fun ret iscons -> ret ^ "\n ?" ^ (sprintf "%d: %s" (Z3.FuncDecl.get_id iscons) (Z3.FuncDecl.to_string iscons))
      )
  )

let z3_dtenv_of_dtenv ctx dtenv =
  (* Debug.print @@ lazy ("mk z3 dtenv from:\n" ^ (LogicOld.DTEnv.str_of dtenv)); *)
  let z3_dtenv = Map.Poly.fold dtenv ~init:(Set.Poly.empty) ~f:(
      fun ~key ~data env -> 
        (* Debug.print @@ lazy (sprintf "mk sort:%s \n%s" key (LogicOld.Datatype.str_of data)); *)
        if Set.Poly.exists env ~f:(
            fun (dt, _) -> Stdlib.(=) key (LogicOld.Datatype.full_name_of dt)
          ) 
        then env 
        else begin
          let dts = LogicOld.Datatype.full_dts_of data in
          let (dt_names, dt_conses) = List.unzip @@ List.map dts ~f:(
              fun dt -> 
                let dt_name = LogicOld.Datatype.full_name_of_dt dt in
                let conses = LogicOld.Datatype.conses_of_dt dt in
                let conses' = List.map conses ~f:(
                    fun cons -> 
                      let name = LogicOld.Datatype.name_of_cons cons in
                      (* Debug.print @@ lazy (sprintf "mk cons:[%s]" name); *)
                      let is_cons_name = Z3.Symbol.mk_string ctx @@ ("is_" ^ name) in
                      (* Debug.print @@ lazy (sprintf "mk is_cons:[%s]" @@ Z3.Symbol.to_string is_cons_name); *)
                      let sels_names, ret_sorts, ref_sorts = 
                        List.fold_left (LogicOld.Datatype.sels_of_cons cons) ~init:([], [], []) ~f:(
                          fun (sels_names, ret_sorts, ref_sorts) sel -> 
                            match sel with
                            | LogicOld.Datatype.Sel (name, ret_sort) -> 
                              (* Debug.print @@ lazy (sprintf "mk sel:[%s]" name); *)
                              (Z3.Symbol.mk_string ctx @@ name)::sels_names, (Some (of_sort ctx env ret_sort))::ret_sorts, 0::ref_sorts
                            | LogicOld.Datatype.InSel (name, ret_name, args) -> 
                              (* Debug.print @@ lazy (sprintf "mk insel:[%s]" name); *)
                              let full_name = List.fold_left args ~init:ret_name ~f:(fun ret arg -> ret ^ LogicOld.Term.str_of_sort arg) in
                              match Set.Poly.find env ~f:(
                                  fun (dt, _) -> Stdlib.(=) full_name (LogicOld.Datatype.full_name_of dt)
                                ) with
                              | Some (_, sort) -> 
                                (Z3.Symbol.mk_string ctx @@ name)::sels_names, (Some (sort))::ret_sorts, 0::ref_sorts
                              | None -> 
                                match List.findi dts ~f:(fun _ dt -> Stdlib.(=) (LogicOld.Datatype.name_of_dt dt) (ret_name)) with
                                | Some (i, _) -> 
                                  (* Debug.print @@ lazy (sprintf "ref id:%d" i); *)
                                  (Z3.Symbol.mk_string ctx @@ full_name)::sels_names, None::ret_sorts, (i)::ref_sorts
                                | _ -> assert false
                        ) in
                      let z3cons = 
                        Z3.Datatype.mk_constructor ctx 
                          (Z3.Symbol.mk_string ctx name) 
                          is_cons_name 
                          (List.rev sels_names)
                          (List.rev ret_sorts)
                          (List.rev ref_sorts) in
                      (* Debug.print @@ lazy ("z3 tester: " ^ (Z3.Datatype.Constructor.get_tester_decl z3cons |> Z3.FuncDecl.to_string)); *)
                      (* List.iter (Z3.Datatype.Constructor.get_accessor_decls z3cons) ~f:(
                         fun sel -> Debug.print @@ lazy ("z3 sel:" ^ Z3.FuncDecl.to_string sel);
                         ); *)
                      z3cons
                  ) in
                dt_name, conses'
            ) in
          let sorts = Z3.Datatype.mk_sorts_s ctx dt_names dt_conses in
          List.fold2_exn dts sorts ~init:env ~f:(
            fun env dt sort -> Set.Poly.add env (LogicOld.Datatype.update_name (LogicOld.Datatype.update_dts data dts) @@ LogicOld.Datatype.name_of_dt dt, sort)
          )
        end
    ) in
  (* Debug.print @@ lazy (str_of_z3_env z3_dtenv); *)
  z3_dtenv


let z3_dtenv_of ctx phi =
  let dtenv = LogicOld.DTEnv.of_formula phi in
  (* Debug.print @@ lazy ("mk z3 dtenv from:\n" ^ (LogicOld.DTEnv.str_of dtenv)); *)
  z3_dtenv_of_dtenv ctx dtenv


let z3_dt_of (dtenv:dtenv) dt =
  snd @@ Set.Poly.find_exn dtenv ~f:(
    fun (dt1, _) -> Stdlib.(=) (LogicOld.Datatype.full_name_of dt) (LogicOld.Datatype.full_name_of dt1)
  )

let z3_cons_of (dtenv:dtenv) dt name =
  let z3_sort = z3_dt_of dtenv dt in
  let z3_conses = Z3.Datatype.get_constructors z3_sort in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_conses) ~f:(
    fun (cons, z3_cons) -> if Stdlib.(=) (Datatype.name_of_cons cons) name then Some (z3_cons) else None
  )

let z3_sel_of (dtenv:dtenv) dt name =
  let z3_sort = z3_dt_of dtenv dt in
  let z3_selss = Z3.Datatype.get_accessors z3_sort in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_selss) ~f:(
    fun (cons, z3_sels) ->
      let sels = Datatype.sels_of_cons cons in
      List.find_map (List.zip_exn sels z3_sels) ~f:(
        fun (sel, z3_sel) -> if (Stdlib.(=) name (Datatype.name_of_sel sel)) then Some(z3_sel) else None
      )
  )

let z3_iscons_of (dtenv:dtenv) dt name =
  let z3_sort = z3_dt_of dtenv dt in
  let z3_testers = Z3.Datatype.get_recognizers z3_sort in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_testers) ~f:(
    fun (cons, z3_tester) -> if Stdlib.(=) (Datatype.name_of_cons cons) name then Some (z3_tester) else None
  )

let penv_of phi ctx dtenv =
  let psenv = Formula.pred_sort_env_of phi |> Set.Poly.to_list in
  List.map psenv ~f:(
    fun (pvar, sorts) ->
      let func = FuncDecl.mk_func_decl_s ctx (Ident.name_of_pvar pvar) (List.map sorts ~f:(of_sort ctx dtenv)) (Boolean.mk_sort ctx) in
      (pvar, func)
  )

(* from our formula to Z3 expr *)
(* of_formula: Z3.context -> (Ident.tvar, Sort.t) Env.t -> info Logic.Formula.t *)
let rec of_formula ctx 
    (env: (Ident.tvar, Sort.t) Env.t) 
    (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) 
    (fenv : fenv) 
    (dtenv : (LogicOld.Datatype.t *Z3.Sort.sort) Set.Poly.t)
    phi = 
  (* Debug.print @@ lazy ("of_formula:" ^ Formula.str_of phi); *)
  if Formula.is_atom phi then 
    let atom, _ = Formula.let_atom phi in
    if Atom.is_pvar_app atom then 
      let pvar, sorts, _, _ = Atom.let_pvar_app atom in
      let func = FuncDecl.mk_func_decl_s ctx (Ident.name_of_pvar pvar) (List.map sorts ~f:(of_sort ctx dtenv)) (Boolean.mk_sort ctx) in
      let penv = Env.update [(pvar, func)] penv in
      of_atom ctx env penv fenv dtenv atom
    else of_atom ctx env penv fenv dtenv atom
  else if Formula.is_neg phi then
    Boolean.mk_not ctx @@ of_formula ctx env penv fenv dtenv @@ fst (Formula.let_neg phi)
  else if Formula.is_and phi then
    let phi1, phi2, _ = Formula.let_and phi in
    Boolean.mk_and ctx [of_formula ctx env penv fenv dtenv phi1; of_formula ctx env penv fenv dtenv phi2]
  else if Formula.is_or phi then
    let phi1, phi2, _ = Formula.let_or phi in
    Boolean.mk_or ctx [of_formula ctx env penv fenv dtenv phi1; of_formula ctx env penv fenv dtenv phi2]
  else if Formula.is_iff phi then
    let phi1, phi2, _ = Formula.let_iff phi in
    Boolean.mk_iff ctx (of_formula ctx env penv fenv dtenv phi1) (of_formula ctx env penv fenv dtenv phi2)
  else if Formula.is_imply phi then
    let phi1, phi2, _ = Formula.let_imply phi in
    Boolean.mk_implies ctx (of_formula ctx env penv fenv dtenv phi1) (of_formula ctx env penv fenv dtenv phi2)
  else if Formula.is_bind phi then
    let binder, bounds, body, _ = Formula.let_bind phi in
    let builder =
      if Stdlib.(=) binder Formula.Forall then Quantifier.mk_forall
      else if Stdlib.(=) binder Formula.Exists then Quantifier.mk_exists
      else assert false
    in
    let bounds = List.rev (SortEnv.list_of bounds) in
    let env = Env.update bounds env in
    let sorts = Env.elems bounds |> List.map ~f:(of_sort ctx dtenv) in
    let vars = Env.keys bounds |> List.map ~f:(of_var ctx) in
    let body = of_formula ctx env penv fenv dtenv body in
    builder ctx sorts vars body None [] [] None None
    |> Quantifier.expr_of_quantifier
  else if Formula.is_letrec phi then
    match Formula.let_letrec phi with
    | [], phi, _ -> of_formula ctx env penv fenv dtenv phi
    | _, _, _ ->
      failwith @@ "underlying solver can not deal with fixpoint predicate : " ^ Formula.str_of phi;
  else failwith (Formula.str_of phi)

and of_var_term ctx env dtenv t =
  let var, sort, _ = Term.let_var t in
  (* Debug.print @@ lazy (sprintf "z3_of_var_term:%s %s" (Ident.name_of_tvar var) (Term.str_of_sort @@ Term.sort_of t)); *)
  match Env.lookupi var env with
  | Some(sort', i) ->
    assert (Stdlib.(=) sort sort');
    (* Debug.print @@ lazy ("mk quantifier"); *)
    let sort = of_sort ctx dtenv sort in
    Quantifier.mk_bound ctx i sort
  | None ->
    (* Debug.print @@ lazy ("mk const var"); *)
    let symbol = of_var ctx var in
    let sort = of_sort ctx dtenv sort in
    Expr.mk_const ctx symbol sort

(* from our term to Z3 expr *)
and of_term ctx 
    (env: (Ident.tvar, Sort.t) Env.t) 
    (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) 
    (fenv : fenv)
    (dtenv : (LogicOld.Datatype.t *Z3.Sort.sort) Set.Poly.t) t =
  (* Debug.print @@ lazy ("of_term :" ^ (Term.str_of t)); *)
  if Term.is_var t then
    of_var_term ctx env dtenv t
  else if Term.is_app t then
    match Term.let_app t with
    | T_bool.Formula phi, [], _ -> of_formula ctx env penv fenv dtenv phi
    | T_bool.IfThenElse, [cond; then_; else_], _ ->
      let cond = of_term ctx env penv fenv dtenv cond in
      let then_ = of_term ctx env penv fenv dtenv then_ in
      let else_ = of_term ctx env penv fenv dtenv else_ in
      Boolean.mk_ite ctx cond then_ else_
    | T_int.Int n, [], _ -> Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n)
    | T_real.Real r, [], _ -> Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
    | (T_int.Add | T_real.RAdd), [t1; t2], _ ->
      Arithmetic.mk_add ctx [of_term ctx env penv fenv dtenv t1; of_term ctx env penv fenv dtenv t2]
    | (T_int.Sub | T_real.RSub), [t1; t2], _ ->
      Arithmetic.mk_sub ctx [of_term ctx env penv fenv dtenv t1; of_term ctx env penv fenv dtenv t2]
    | (T_int.Mult | T_real.RMult), [t1; t2], _ ->
      Arithmetic.mk_mul ctx [of_term ctx env penv fenv dtenv t1; of_term ctx env penv fenv dtenv t2]
    | T_int.Div, [t1; t2], _ ->
      Arithmetic.mk_div ctx (of_term ctx env penv fenv dtenv t1) (of_term ctx env penv fenv dtenv t2)
    | T_int.Mod, [t1; t2], _ ->
      Arithmetic.Integer.mk_mod ctx (of_term ctx env penv fenv dtenv t1) (of_term ctx env penv fenv dtenv t2)
    | T_int.Rem, [t1; t2], _ ->
      Arithmetic.Integer.mk_rem ctx (of_term ctx env penv fenv dtenv t1) (of_term ctx env penv fenv dtenv t2)
    | T_real.RDiv, [t1; t2], _ ->
      Arithmetic.mk_div ctx
        (Arithmetic.Integer.mk_int2real(*ToDo: remove*) ctx @@ of_term ctx env penv fenv dtenv t1)
        (Arithmetic.Integer.mk_int2real(*ToDo: remove*) ctx @@ of_term ctx env penv fenv dtenv t2)
    | (T_int.Neg | T_real.RNeg), [t], _ ->
      Arithmetic.mk_unary_minus ctx (of_term ctx env penv fenv dtenv t)
    | (T_int.Abs | T_real.RAbs) as op, [t], _ ->
      let n = of_term ctx env penv fenv dtenv t in
      let minus_n = Arithmetic.mk_unary_minus ctx n in
      let is_minus = Arithmetic.mk_lt ctx n
          (match op with
           | T_int.Abs -> Arithmetic.Integer.mk_numeral_i ctx 0
           | T_real.RAbs -> Arithmetic.Real.mk_numeral_i ctx 0
           | _ -> assert false) in
      Boolean.mk_ite ctx is_minus minus_n n
    | (T_int.Power | T_real.RPower), [t1; t2], _ ->
      Arithmetic.mk_power ctx (of_term ctx env penv fenv dtenv t1) (of_term ctx env penv fenv dtenv t2)
    | FVar (var, sorts), ts, _ ->
      let symbol = of_var ctx var in
      let sorts = List.map ~f:(of_sort ctx dtenv) sorts in
      let sargs, sret = List.take sorts (List.length sorts - 1), List.last_exn sorts in
      let ts = List.map ~f:(of_term ctx env penv fenv dtenv) ts in
      Expr.mk_app ctx (FuncDecl.mk_func_decl ctx symbol sargs sret) ts
    | T_recfvar.RecFVar(fname, args, ret_sort, body), ts, _ ->
      let func = Z3.FuncDecl.mk_rec_func_decl_s ctx (Ident.name_of_tvar fname) (List.map args ~f:(fun (_, sort) -> of_sort ctx dtenv sort)) (of_sort ctx dtenv ret_sort) in
      if not @@ (Term.is_var body) then
        Z3.FuncDecl.add_rec_def ctx func (List.map args ~f:(fun (tvar, sort) -> of_var_term ctx env dtenv (Term.mk_var tvar sort))) (of_term ctx env penv fenv dtenv body);
      Z3.FuncDecl.apply func (List.map ts ~f:(of_term ctx env penv fenv dtenv))
    | T_real_int.ToReal, [t], _ ->
      Arithmetic.Integer.mk_int2real ctx (of_term ctx env penv fenv dtenv t)
    | T_real_int.ToInt, [t], _ ->
      Arithmetic.Real.mk_real2int ctx (of_term ctx env penv fenv dtenv t)
    | T_array.AStore, [t1; t2; t3], _ -> 
      let zt1 = of_term ctx env penv fenv dtenv t1 in
      let zt2 = of_term ctx env penv fenv dtenv t2 in
      let zt3 = of_term ctx env penv fenv dtenv t3 in
      Z3Array.mk_store ctx zt1 zt2 zt3
    | T_array.ASelect, [t1; t2;], _ -> 
      let zt1 = of_term ctx env penv fenv dtenv t1 in
      let zt2 = of_term ctx env penv fenv dtenv t2 in
      Z3Array.mk_select ctx zt1 zt2
    | T_array.AConst (T_array.SArray(si, _se)), [t1], _ -> 
      Z3Array.mk_const_array ctx (of_sort ctx dtenv si) (of_term ctx env penv fenv dtenv t1)
    | T_dt.DTCons (name, _, dt), ts, _ ->
      let ts = List.map ts ~f:(of_term ctx env penv fenv dtenv) in
      let dt_cons = z3_cons_of dtenv dt name in
      Z3.FuncDecl.apply dt_cons ts
    | T_dt.DTSel (name, dt, _), ts, _ -> 
      let ts = List.map ts ~f:(of_term ctx env penv fenv dtenv) in
      let dt_sel = z3_sel_of dtenv dt name in
      Z3.FuncDecl.apply dt_sel ts 
    | _ -> failwith (Term.str_of t)
  else failwith (Term.str_of t)
and
  (* from our atom to Z3 expr *)
  of_atom ctx
    (env: (Ident.tvar, Sort.t) Env.t)
    (penv: (Ident.pvar, FuncDecl.func_decl) Env.t) 
    (fenv : fenv)
    (dtenv : (LogicOld.Datatype.t *Z3.Sort.sort) Set.Poly.t) atom =
  (* Debug.print @@ lazy (sprintf "z3_of_atom:%s" (Atom.str_of atom)); *)
  if Atom.is_true atom then
    Boolean.mk_true ctx
  else if Atom.is_false atom then
    Boolean.mk_false ctx
  else if Atom.is_psym_app atom then
    let sym, args, _ = Atom.let_psym_app atom in
    match sym, List.map ~f:(of_term ctx env penv fenv dtenv) args with
    | T_bool.Eq, [t1; t2] -> Boolean.mk_eq ctx t1 t2
    | T_bool.Neq, [t1; t2] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx t1 t2
    | (T_int.Leq | T_real.RLeq), [t1; t2] -> Arithmetic.mk_le ctx t1 t2
    | (T_int.Geq | T_real.RGeq), [t1; t2] -> Arithmetic.mk_ge ctx t1 t2
    | (T_int.Lt | T_real.RLt), [t1; t2] -> Arithmetic.mk_lt ctx t1 t2
    | (T_int.Gt | T_real.RGt), [t1; t2] -> Arithmetic.mk_gt ctx t1 t2
    | T_int.PDiv, [t1; t2] -> Boolean.mk_eq ctx (Arithmetic.Integer.mk_mod ctx t2 t1) (Arithmetic.Integer.mk_numeral_i ctx 0)
    | T_int.NPDiv, [t1; t2] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx (Arithmetic.Integer.mk_mod ctx t2 t1) (Arithmetic.Integer.mk_numeral_i ctx 0)
    | T_real_int.IsInt, [t] -> Arithmetic.Real.mk_is_integer ctx t
    | T_dt.IsCons (name, dt), ts ->
      let iscons = z3_iscons_of dtenv dt name in
      Z3.FuncDecl.apply iscons ts
    | T_dt.IsNotCons (name, dt), ts ->
      let iscons = z3_iscons_of dtenv dt name in
      Boolean.mk_not ctx @@ Z3.FuncDecl.apply iscons ts
    | _ -> assert false (* TODO: implement *)
  else if Atom.is_pvar_app atom then
    let (pvar, _sargs, args, _) = Atom.let_pvar_app atom in
    if List.is_empty args then of_var_term ctx env dtenv(Term.mk_var (Ident.Tvar(Ident.name_of_pvar pvar)) T_bool.SBool)
    else 
      let pred = 
        try Env.lookup_exn pvar penv
        with Caml.Not_found -> failwith ("not supported: " ^ Ident.name_of_pvar pvar)
      in
      Expr.mk_app ctx pred (List.map ~f:(fun arg -> of_term ctx env penv fenv dtenv arg) args)
  else failwith (Atom.str_of atom)

let check_sat_z3 ?(timeout=None) ctx dtenv phis =
  let solver = Z3.Solver.mk_solver ctx None in
  (match timeout with
   | None -> ()
   | Some timeout ->
     let params = Z3.Params.mk_params ctx in
     Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
     Z3.Solver.set_parameters solver params);
  Z3.Solver.add solver phis;
  match Z3.Solver.check solver [] with
  | SATISFIABLE -> (match Z3.Solver.get_model solver with
      | Some model ->
        let model = model_of dtenv model in
        (* debug_print_z3_model model; *)
        `Sat model
      | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE -> `Unsat
  | UNKNOWN -> (match Z3.Solver.get_reason_unknown solver with
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
    let num_sat = Map.Poly.fold soft ~init:0 ~f:(fun ~key:_ ~data sum ->
        List.fold data ~init:sum ~f:(fun sum (expr, weight) ->
            sum + (match Model.eval model expr true with
                | None -> 0 | Some e -> if Boolean.is_true e then weight else 0))) in
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
    let lower = Optimize.get_lower handle |> term_of Env.empty Env.empty dtenv in
    let upper = Optimize.get_upper handle |> term_of Env.empty Env.empty dtenv in
    Some (lower, upper, model_of dtenv model)
  | _ -> None

let check_sat ?(timeout=None) fenv phis =
  let cfg = [ ("model", "true"); ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  let cfg = match timeout with
    | None -> cfg
    | Some timeout -> cfg @ [("timeout", string_of_int @@ timeout)] in
  let ctx = mk_context cfg in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of phis in
  debug_print_z3_input phis;
  let phis = List.map phis ~f:(T_recfvar.defined_formula_of fenv) in
  debug_print_z3_input phis;
  let phis' = List.map phis ~f:(of_formula ctx Env.empty Env.empty fenv dtenv) in
  (* match check_sat_z3 ~timeout:(Some 5000) ctx dtenv phis' with
     |`Sat model -> `Sat model
     |`Unsat -> `Unsat
     | _ ->
     let phis = List.map phis ~f:(T_recfvar.defined_formula_of fenv) in
     debug_print_z3_input phis;
     let phis' = List.map phis ~f:(of_formula ctx Env.empty Env.empty fenv dtenv) in *)
  check_sat_z3 ~timeout ctx dtenv phis'

let check_sat_unsat_core_main ?(timeout=None) solver ctx fenv dtenv pvar_clause_map =
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
      Debug.print @@ lazy (sprintf "assert and track: [%s] %s" name (Formula.str_of phi));
      let phi_expr = of_formula ctx Env.empty Env.empty fenv dtenv phi in
      Z3.Solver.assert_and_track solver phi_expr (Boolean.mk_const_s ctx name));
  match Z3.Solver.check solver [] with
  | Z3.Solver.SATISFIABLE -> (match Z3.Solver.get_model solver with
      | Some model ->
        let model = model_of dtenv model in
        `Sat model
      | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE -> 
    let unsat_keys = List.map ~f:Z3.Expr.to_string @@ Z3.Solver.get_unsat_core solver in
    Debug.print @@ lazy "unsat reason:";
    List.iter unsat_keys ~f:(fun unsat_key -> Debug.print @@ lazy (unsat_key));
    `Unsat (unsat_keys)
  | UNKNOWN -> (match Z3.Solver.get_reason_unknown solver with
      | "timeout" | "canceled" -> `Timeout
      | reason -> `Unknown reason)
let check_sat_unsat_core_main ?(timeout=None) solver ctx fenv dtenv pvar_clause_map =
  match timeout with
  | None ->
    check_sat_unsat_core_main ~timeout solver ctx fenv dtenv pvar_clause_map
  | Some tm ->
    if tm = 0 then `Timeout(* times out immediately *) else
      Timer.enable_timeout (tm / 1000) ident ignore
        (fun () -> check_sat_unsat_core_main ~timeout solver ctx fenv dtenv pvar_clause_map)
        (fun _ res -> res)
        (fun _ -> function Timer.Timeout -> `Timeout | e -> raise e)


let check_sat_unsat_core ?(timeout=None) fenv pvar_clause_map =
  let ctx =
    let cfg = [ ("model", "true"); ("unsat_core", "true") ] in
    let cfg = if validate then cfg @ validate_cfg else cfg in
    let cfg = match timeout with
      | None -> cfg
      | Some timeout -> cfg @ [("timeout", string_of_int timeout)] in
    mk_context cfg in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of @@ snd @@ List.unzip @@ Map.Poly.to_alist pvar_clause_map in
  let solver = Z3.Solver.mk_solver ctx None in
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
  let hard = List.map hard ~f:(of_formula ctx Env.empty Env.empty fenv dtenv) in
  let soft = Map.Poly.map soft ~f:(List.map ~f:(fun (phi, weight) -> of_formula ctx Env.empty Env.empty fenv dtenv phi , weight)) in
  max_smt_z3 ctx dtenv hard soft
(** ToDo: use MaxSMT instead *)
let max_smt_of fenv num_ex phis =
  let ctx = mk_context [("unsat_core", "true")] in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of phis in
  let name_map0 =
    List.map phis ~f:(of_formula ctx Env.empty Env.empty fenv dtenv)
    |> List.foldi ~init:Map.Poly.empty ~f:(fun i map phi ->
        let name = Boolean.mk_const_s ctx @@ "#S_" ^ (string_of_int i) in
        Map.Poly.update map name ~f:(function None -> phi | Some x -> x)) in
  let rec inner num_ex models ignored name_map =
    if num_ex <= 0 then models
    else
      let solver = Z3.Solver.mk_solver ctx None in
      Map.Poly.iteri name_map ~f:(fun ~key ~data -> Z3.Solver.assert_and_track solver data key);
      match Z3.Solver.check solver [] with
      | Z3.Solver.SATISFIABLE ->
        (match Z3.Solver.get_model solver with
         | None -> assert false
         | Some model ->
           let models' = Set.Poly.add models (model_of dtenv model) in
           let name_map' = Map.Poly.filter_keys ~f:(Set.Poly.mem ignored) name_map0 in
           inner (num_ex - 1) models' Set.Poly.empty name_map')
      | UNSATISFIABLE ->
        let ucore = List.hd_exn @@ Z3.Solver.get_unsat_core solver in
        inner num_ex models (Set.Poly.add ignored ucore) (Map.Poly.remove name_map ucore)
      | UNKNOWN -> assert false
  in
  inner num_ex Set.Poly.empty Set.Poly.empty name_map0

let check_opt_maximize fenv phis obj =
  let cfg = [ ("model", "true") ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  let ctx = mk_context cfg in
  let dtenv = z3_dtenv_of ctx @@ Formula.and_of phis in
  debug_print_z3_input phis;
  let phis = List.map phis ~f:(fun phi -> of_formula ctx Env.empty Env.empty fenv dtenv phi) in
  let obj = of_term ctx Env.empty Env.empty fenv dtenv obj in
  check_opt_maximize_z3 ctx dtenv phis obj

let check_valid fenv phi =
  match check_sat fenv[Formula.mk_neg phi] with
  | `Unsat -> `Valid
  | `Sat model -> `Invalid model
  | res -> res

let is_valid fenv phi = match check_valid fenv phi with `Valid -> true | _ -> false
let is_sat fenv phi = match check_sat fenv [phi] with `Sat _ -> true | _ -> false

let qelim fenv phi =
  if Formula.is_bind phi then
    let ctx = mk_context [] in
    let dtenv = z3_dtenv_of ctx @@ phi in
    let goal = Z3.Goal.mk_goal ctx false false false in
    let phi = of_formula ctx Env.empty Env.empty fenv dtenv phi in
    Z3.Goal.add goal [phi];
    let g = Z3.Tactic.ApplyResult.get_subgoal (Z3.Tactic.apply (Z3.Tactic.mk_tactic ctx "qe") goal None) 0 in
    let phi = formula_of Env.empty Env.empty dtenv @@ Z3.Expr.simplify (Goal.as_expr g) None in
    (*print_endline @@ Formula.str_of phi;*)
    phi
  else phi

let smtlib2_str_of_formula ctx fenv dtenv phi =
  let phi = of_formula ctx (Formula.term_sort_env_of phi |> Set.Poly.to_list) (penv_of phi ctx dtenv) fenv dtenv phi in
  Expr.to_string phi



let expr_of ctx fenv dtenv phi =
  try of_formula ctx Env.empty Env.empty fenv dtenv @@ Evaluator.simplify phi
  with _ -> of_formula ctx Env.empty Env.empty fenv dtenv @@ Formula.mk_true ()
let str_of_asserts_of_solver solver =
  "Asserts of solver:" ^
  String.concat ~sep:"\n\t" @@ List.map ~f:Expr.to_string @@ Z3.Solver.get_assertions solver
let check_valid_inc solver phis =
  match Z3.Solver.check solver phis with
  | SATISFIABLE -> 
    Debug.print @@ lazy (sprintf "%s \n check valid -> (sat)invalid" (str_of_asserts_of_solver solver));
    false
  | _ -> 
    Debug.print @@ lazy (sprintf "%s \n checksat valid -> (unsat)valid" (str_of_asserts_of_solver solver));
    true
let star and_flag = function
  | Formula.Atom (a, _) when Atom.is_pvar_app a -> None
  | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _) when Atom.is_pvar_app a -> None
  | phi -> Some (Evaluator.simplify @@ if and_flag then phi else Formula.mk_neg phi)
let rec simplify_term  solver ctx fenv dtenv = function
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
    let args', _has_changed_list = List.unzip @@ List.map ~f:(simplify_term solver ctx fenv dtenv) args in
    Atom.mk_pvar_app pvar sorts args' ~info,
    false(*List.exists ~f:ident has_changed_list*)
  else
    let phi = Formula.mk_atom atom in
    (* Debug.print @@ lazy (sprintf "simplify atom: %s" (Formula.str_of phi)); *)
    if check_valid_inc solver [expr_of ctx fenv dtenv @@ Formula.mk_neg phi] then Atom.mk_true (), true
    else if check_valid_inc solver [expr_of ctx fenv dtenv @@ phi] then Atom.mk_false (), true
    else atom, false
and check_sub_formulas solver ctx fenv (dtenv:dtenv) and_flag phi =
  let cs = Set.Poly.to_list @@ if and_flag then Formula.conjuncts_of phi else Formula.disjuncts_of phi in
  (* Debug.print @@ lazy (sprintf "Cs: %s" (String.concat ~sep:"\n\t" @@ List.map cs ~f:Formula.str_of)); *)
  (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
  Z3.Solver.push solver;
  let cs', _ , has_changed =
    List.fold_left cs ~init:([], List.tl_exn cs, false) ~f:(
      fun (cs', cs, has_changed) c ->
        (* Debug.print @@ lazy (sprintf "c: %s" (Formula.str_of c)); *)
        Z3.Solver.push solver;
        Z3.Solver.add solver @@ List.map ~f:(expr_of ctx fenv dtenv) @@ List.filter_map cs ~f:(star and_flag);
        (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
        let c', has_changed' = simplify_formula solver ctx fenv dtenv c in
        Z3.Solver.pop solver 1;
        (* Debug.print @@ lazy (sprintf "c': %s" (Formula.str_of c')); *)
        (match star and_flag c' with Some phi -> Z3.Solver.add solver [expr_of ctx fenv dtenv phi] | None -> ());
        (c' :: cs'), (match cs with |_::tl -> tl |_ -> []),
        has_changed || has_changed') in
  Z3.Solver.pop solver 1;
  let cs' = List.rev cs' in
  (* Debug.print @@ lazy (sprintf "compare Cs to Cs':\nCs :%s" (String.concat ~sep:"\n\t" @@ List.map cs ~f:Formula.str_of)); *)
  (* Debug.print @@ lazy (sprintf "Cs': %s" (String.concat ~sep:"\n\t" @@ List.map cs' ~f:Formula.str_of)); *)
  let ret = Evaluator.simplify @@ if and_flag then Formula.and_of cs' else Formula.or_of cs' in
  if has_changed then begin
    (* Debug.print @@ lazy ("has changed."); *)
    fst @@ check_sub_formulas solver ctx fenv dtenv and_flag ret, true
  end else ret, false
and simplify_formula solver ctx fenv (dtenv:dtenv) phi =
  (* Debug.print @@ lazy (sprintf "simplify formula: %s" (Formula.str_of phi) ); *)
  (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
  match phi with
  | Formula.Atom (atom, _) when not @@ (Atom.is_true atom || Atom.is_false atom) ->
    let atom, has_changed = simplify_atom solver ctx fenv dtenv atom in
    Formula.mk_atom atom, has_changed
  | Formula.UnaryOp(Not, Atom (atom, _), _) when not @@ (Atom.is_true atom || Atom.is_false atom) ->
    let atom, has_changed = simplify_atom solver ctx fenv dtenv atom in
    Formula.mk_neg (Formula.mk_atom atom), has_changed
  | Formula.BinaryOp(And, _, _, _) -> check_sub_formulas solver ctx fenv dtenv true phi
  | Formula.BinaryOp(Or, _, _, _) -> check_sub_formulas solver ctx fenv dtenv false phi
  | _ -> phi, false
and simplify ?(timeout=None) fenv phi =
  Debug.print @@ lazy ("===========simplify start=============");
  Debug.print @@ lazy (sprintf "the formula:\n\t%s" @@ Formula.str_of phi);
  let cfg = match timeout with
    | None -> []
    | Some timeout -> [("timeout", string_of_int timeout)] in
  let ctx = mk_context cfg in
  let dtenv = z3_dtenv_of ctx @@ phi in
  (* Debug.print @@ lazy (sprintf "the smtlib2 formua:\n\t%s" @@ smtlib2_str_of_formula ctx dtenv phi); *)
  let solver = Z3.Solver.mk_solver ctx None in
  (match timeout with
   | None -> ()
   | Some timeout ->
     let params = Z3.Params.mk_params ctx in
     Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
     Z3.Solver.set_parameters solver params);
  let ret = Evaluator.simplify @@ fst @@ simplify_formula solver ctx fenv dtenv @@ Evaluator.simplify @@ Formula.nnf_of phi in
  Debug.print @@ lazy (sprintf "result: %s\n===========simplify end=============" @@ Formula.str_of ret);
  ret

