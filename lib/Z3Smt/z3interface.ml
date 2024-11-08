open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

let verbose = false

module Debug =
  Debug.Make ((val Debug.Config.(if verbose then enable else disable)))

let debug_print_z3_input phis =
  Debug.print @@ lazy "Z3 input formulas:";
  List.iter phis ~f:(fun phi -> Debug.print @@ lazy (Formula.str_of phi))

let debug_print_z3_model model =
  Debug.print @@ lazy ("Z3 output model: " ^ str_of_model model)

let validate = false
let validate_cfg = [ ("model_validate", "true"); ("well_sorted_check", "true") ]

(* let _ = Z3.set_global_param "smt.macro_finder" "true" *)

(* Environments *)
type dtenv = (Datatype.t * Z3.Sort.sort) Set.Poly.t
type fenv = (Ident.tvar, Z3.FuncDecl.func_decl) Map.Poly.t

(* For concurrency control *)
let mutex = Caml_threads.Mutex.create ()
let enable_mutex = false
let lock () = if enable_mutex then Caml_threads.Mutex.lock mutex
let unlock () = if enable_mutex then Caml_threads.Mutex.unlock mutex

(* Solver pool *)
let enable_solver_pool = true

type instance = {
  ctx : Z3.context;
  solver : Z3.Solver.solver;
  goal : Z3.Goal.goal;
  cfg : (string * string) list;
  mutable dtenv : dtenv;
  mutable fenv : fenv;
}

let get_instance =
  let new_instance cfg =
    Caml_threads.Mutex.lock mutex;
    Gc.full_major ();
    let ctx = Z3.mk_context cfg in
    let solver = Z3.Solver.mk_solver ctx None in
    let goal = Z3.Goal.mk_goal ctx false false false in
    let dtenv = Set.Poly.empty in
    let fenv = Map.Poly.empty in
    Caml_threads.Mutex.unlock mutex;
    { ctx; solver; goal; dtenv; fenv; cfg }
  in
  fun (id : int option) cfg instance_pool ->
    if not enable_solver_pool then new_instance cfg
    else
      match Hashtbl.Poly.find instance_pool (id, cfg) with
      | None -> new_instance cfg
      | Some instance -> instance

let back_instance ~reset instance_pool id instance =
  if enable_solver_pool then (
    reset instance;
    Hashtbl.Poly.set instance_pool ~key:(id, instance.cfg) ~data:instance)

let instance_pool = Hashtbl.Poly.create ()
let clean () = (* Hashtbl.Poly.clear cache; *) Hashtbl.Poly.clear instance_pool

(** decoding *)

let unint_svar_prefix = "#svar_"
let unint_arrow_prefix = "#arrow_"
let unint_is_cons_prefix = "#is_"
let unint_tuple_prefix = "#tuple"
let unint_tuple_sel_prefix = "#t_sel."
let unint_epsilon = "#epsilon"
let unint_symbol_prefix = "#symbol_"
let unint_concat_fin = "#concat_fin"
let unint_concat_inf = "#concat_inf"
let unint_is_prefix_of_fin = "#is_prefix_of_fin"
let unint_is_prefix_of_inf = "#is_prefix_of_inf"
let unint_is_in_reg_exp_fin_prefix = "#is_in_reg_exp_fin"
let unint_is_in_reg_exp_inf_prefix = "#is_in_reg_exp_inf"
let unint_unsupported = "unsupported"
let unint_finseq = "#fin_seq"
let unint_infseq = "#inf_seq"
let unescape_z3 = String.substr_replace_all ~pattern:"|" ~with_:"" (*ToDo*)
let divide_str = "__separator__"
(*let var_of s =
  Scanf.unescaped @@ (try Scanf.sscanf s "|%s@|" Fn.id with _ -> s)
  |> Str.split (Str.regexp divide_str)
  |> List.hd_exn*)

let rec sort_of z3_dtenv s =
  (*print_endline @@ "converting " ^ Z3.Sort.to_string s;*)
  match Z3.Sort.get_sort_kind s with
  | Z3enums.UNINTERPRETED_SORT ->
      let name = Z3.Symbol.get_string @@ Z3.Sort.get_name s in
      if String.is_prefix ~prefix:unint_svar_prefix name then
        let svar =
          String.sub name
            ~pos:(String.length unint_svar_prefix)
            ~len:(String.length name - String.length unint_svar_prefix)
        in
        Sort.SVar (Ident.Svar svar)
      else if String.is_prefix ~prefix:unint_arrow_prefix name then (
        let s =
          String.sub name
            ~pos:(String.length unint_arrow_prefix)
            ~len:(String.length name - String.length unint_arrow_prefix)
        in
        let c =
          (* ToDo: assuming that LogicOld.ref_dtenv is properly set *)
          (*LogicOld.update_dtenv dtenv;
            if false then
              print_endline @@ sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv;*)
          RtypeParser.comp_ty RtypeLexer.token (Lexing.from_string s)
            Map.Poly.empty (*ToDo*)
        in
        if false then
          print_endline
          @@ sprintf "parsed %s from %s"
               (Rtype.str_of_comp ~config:!Rtype.cgen_config c)
               s;
        Rtype.sort_of_comp c)
      else if String.(name = unint_unsupported) then failwith "not supported"
      else if String.(name = unint_finseq) then T_sequence.SSequence true
      else if String.(name = unint_infseq) then T_sequence.SSequence false
      else T_dt.SUS (name, [])
  | Z3enums.BOOL_SORT -> T_bool.SBool
  | Z3enums.INT_SORT -> T_int.SInt
  | Z3enums.REAL_SORT -> T_real.SReal
  | Z3enums.BV_SORT -> T_bv.SBV (Some (Z3.BitVector.get_size s, true (*ToDo*)))
  | Z3enums.ARRAY_SORT ->
      T_array.SArray
        ( sort_of z3_dtenv @@ Z3.Z3Array.get_domain s,
          sort_of z3_dtenv @@ Z3.Z3Array.get_range s )
  | Z3enums.DATATYPE_SORT -> (
      match Set.find z3_dtenv ~f:(snd >> Stdlib.( = ) s) with
      | Some (dt, _) -> T_dt.SDT dt
      | _ ->
          if
            String.is_prefix ~prefix:unint_tuple_prefix
            @@ unescape_z3 @@ Z3.Sort.to_string s
          then
            T_tuple.STuple
              (List.map ~f:(Z3.FuncDecl.get_range >> sort_of z3_dtenv)
              @@ Z3.Tuple.get_field_decls s)
          else failwith @@ "[z3:sort_of] unknown dt type:" ^ Z3.Sort.to_string s
      )
  | Z3enums.RELATION_SORT -> failwith "RELATION_SORT not supported"
  | Z3enums.FINITE_DOMAIN_SORT -> failwith "FINITE_DOMAIN_SORT not supported"
  | Z3enums.FLOATING_POINT_SORT -> failwith "FLOATING_POINT_SORT not supported"
  | Z3enums.ROUNDING_MODE_SORT -> failwith "ROUNDING_MODE_SORT not supported"
  | Z3enums.SEQ_SORT (*ToDo*) -> T_string.SString
  | Z3enums.RE_SORT -> T_regex.SRegEx
  | Z3enums.CHAR_SORT -> failwith "CHAR_SORT not supported"
  | Z3enums.UNKNOWN_SORT ->
      if String.(Z3.Sort.to_string s = "Proof") then
        Sort.SVar (Ident.Svar "Proof") (*ToDo*)
      else
        failwith @@ "[z3:sort_of] UNKNOWN_SORT not supported:"
        ^ Z3.Sort.to_string s
  | Z3enums.TYPE_VAR -> failwith "TYPE_VAR not supported"

let look_up_func_of_dt dt sort func =
  if Datatype.is_undef dt then `Unkonwn
  else
    let verbose = false in
    if verbose then
      Debug.print
      @@ lazy
           (sprintf "[look_up_func] finding (#%d) %s in %s"
              (Z3.FuncDecl.get_id func)
              (Z3.FuncDecl.to_string func)
              (Z3.Sort.to_string sort));
    let id = Z3.FuncDecl.get_id func in
    let z3_conses = Z3.Datatype.get_constructors sort in
    let z3_selss = Z3.Datatype.get_accessors sort in
    let z3_testers = Z3.Datatype.get_recognizers sort in
    let z3_funcs = List.zip3_exn z3_conses z3_testers z3_selss in
    List.fold2_exn (Datatype.conses_of dt) z3_funcs ~init:`Unkonwn
      ~f:(fun ret cons (z3_cons, z3_tester, z3_sels) ->
        match ret with
        | `Unkonwn ->
            if id = Z3.FuncDecl.get_id z3_cons then (
              if verbose then Debug.print @@ lazy "constructor found";
              `Cons cons)
            else if id = Z3.FuncDecl.get_id z3_tester then (
              if verbose then Debug.print @@ lazy "tester found";
              `IsCons cons)
            else
              List.fold2_exn (Datatype.sels_of_cons cons) z3_sels ~init:ret
                ~f:(fun ret sel z3_sel ->
                  if verbose then
                    Debug.print
                    @@ lazy
                         (sprintf "search_sel %d =? (#%d) %s" id
                            (Z3.FuncDecl.get_id z3_sel)
                            (Z3.FuncDecl.to_string z3_sel));
                  match ret with
                  | `Unkonwn ->
                      if id = Z3.FuncDecl.get_id z3_sel then (
                        if verbose then Debug.print @@ lazy "selector found";
                        `Sel sel)
                      else ret
                  | _ -> ret)
        | _ -> ret)

let look_up_func dtenv func =
  Set.find_map dtenv ~f:(fun (dt, sort) ->
      match look_up_func_of_dt dt sort func with
      | `Unkonwn -> None
      | ret -> Some (dt, ret))

let parse_root_obj = function
  | Sexp.List [ Sexp.Atom "root-obj"; t; n ] ->
      let rec parse_term = function
        | Sexp.Atom "x" -> Term.mk_var (Ident.Tvar "x") T_real.SReal
        | Sexp.Atom ident -> (
            (*try T_int.mk_int (Z.of_string ident) with _ ->*)
            try T_real.mk_real (Q.of_string ident)
            with _ -> failwith "[z3:parse_term]")
        | Sexp.List [ Sexp.Atom "-"; t ] ->
            T_real.mk_rneg (*ToDo*) (parse_term t)
        | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
            List.fold args ~init:(parse_term arg) ~f:(fun acc t ->
                T_real.mk_radd (*ToDo*) acc (parse_term t))
        | Sexp.List (Sexp.Atom "*" :: arg :: args) ->
            List.fold args ~init:(parse_term arg) ~f:(fun acc t ->
                T_real.mk_rmult (*ToDo*) acc (parse_term t))
        | Sexp.List [ Sexp.Atom "^"; t1; t2 ] ->
            T_real.mk_rpower (*ToDo*) (parse_term t1) (parse_term t2)
        | _ -> failwith "[z3:parse_term]"
      in
      let t = parse_term t in
      (t, int_of_string @@ Sexp.to_string n)
  | e ->
      failwith @@ "[z3:parse_root_obj]" ^ Sexp.to_string e ^ " is not root-obj"

let rec apply ctx senv penv dtenv op expr =
  match List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr with
  | e :: es -> List.fold ~init:e es ~f:op
  | _ -> assert false

and apply_uop ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1 ] -> op (term_of ctx senv penv dtenv e1)
  | _ -> assert false

and apply_urel ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1 ] -> op (term_of ctx senv penv dtenv e1)
  | _ -> assert false

and apply_bop ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1; e2 ] ->
      op (term_of ctx senv penv dtenv e1) (term_of ctx senv penv dtenv e2)
  | _ -> assert false

and apply_brel ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1; e2 ] ->
      op (term_of ctx senv penv dtenv e1) (term_of ctx senv penv dtenv e2)
  | _ -> assert false

(* Conversion from Z3 expressions to terms *)
and term_of ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  Debug.print @@ lazy (sprintf "[z3:term_of] %s" @@ Z3.Expr.to_string expr);
  if Z3.Boolean.is_true expr then T_bool.mk_true ()
  else if Z3.Boolean.is_false expr then T_bool.mk_false ()
  else if Z3.Boolean.is_ite expr then
    match Z3.Expr.get_args expr with
    | [ e1; e2; e3 ] ->
        T_bool.ifte
          (formula_of ctx senv penv dtenv e1)
          (term_of ctx senv penv dtenv e2)
          (term_of ctx senv penv dtenv e3)
    | _ -> failwith @@ "[z3:term_of] " ^ Z3.Expr.to_string expr
  else if Z3.Arithmetic.is_int_numeral expr then
    T_int.mk_int @@ Z3.Arithmetic.Integer.get_big_int expr
  else if Z3.Arithmetic.is_rat_numeral expr then
    T_real.mk_real @@ Z3.Arithmetic.Real.get_ratio expr
  else if Z3.Arithmetic.is_algebraic_number expr then
    let t, n = parse_root_obj @@ Sexp.of_string @@ Z3.Expr.to_string expr in
    T_real.mk_alge t n
  else if Z3.BitVector.is_bv_numeral expr then
    let size =
      Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true (*ToDo*))
    in
    T_bv.mk_bvnum ~size @@ Z.of_string @@ Z3.BitVector.numeral_to_string expr
  else if Z3.Arithmetic.is_uminus expr then
    apply_uop ctx senv penv dtenv T_int.mk_neg expr
  else if Z3.Arithmetic.is_int2real expr then
    apply_uop ctx senv penv dtenv T_irb.mk_int_to_real expr
  else if Z3.Arithmetic.is_real2int expr then
    apply_uop ctx senv penv dtenv T_irb.mk_real_to_int expr
  else if Z3.BitVector.is_bv_uminus expr then
    let size =
      Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true (*ToDo*))
    in
    apply_uop ctx senv penv dtenv (T_bv.mk_bvneg ~size) expr
  else if Z3.BitVector.is_int2bv expr then
    let size =
      Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true (*ToDo*))
    in
    apply_uop ctx senv penv dtenv (T_irb.mk_int_to_bv ~size) expr
  else if Z3.BitVector.is_bv2int expr then
    let size =
      match Z3.Expr.get_args expr with
      | [ e ] -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), true (*ToDo*))
      | _ -> failwith "[z3:term_of]"
    in
    apply_uop ctx senv penv dtenv (T_irb.mk_bv_to_int ~size) expr
  else if Z3.Arithmetic.is_add expr then
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply ctx senv penv dtenv T_int.mk_add expr
    | T_real.SReal -> apply ctx senv penv dtenv T_real.mk_radd expr
    | _ ->
        failwith @@ "[z3:term_of]" ^ Z3.Sort.to_string @@ Z3.Expr.get_sort expr
  else if Z3.Arithmetic.is_sub expr then
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply ctx senv penv dtenv T_int.mk_sub expr
    | T_real.SReal -> apply ctx senv penv dtenv T_real.mk_rsub expr
    | _ ->
        failwith @@ "[z3:term_of]" ^ Z3.Sort.to_string @@ Z3.Expr.get_sort expr
  else if Z3.Arithmetic.is_mul expr then
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply ctx senv penv dtenv T_int.mk_mult expr
    | T_real.SReal -> apply ctx senv penv dtenv T_real.mk_rmult expr
    | _ ->
        failwith @@ "[z3:term_of] " ^ Z3.Sort.to_string @@ Z3.Expr.get_sort expr
  else if Z3.Arithmetic.is_idiv expr then
    apply_bop ctx senv penv dtenv T_int.mk_div expr
  else if Z3.Arithmetic.is_div expr then
    apply_bop ctx senv penv dtenv T_real.mk_rdiv expr
  else if Z3.Arithmetic.is_modulus expr then
    apply_bop ctx senv penv dtenv T_int.mk_mod expr
  else if Z3.Arithmetic.is_remainder expr then
    apply_bop ctx senv penv dtenv T_int.mk_rem expr
  else if Z3.BitVector.is_bv_add expr then
    let size =
      Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true (*ToDo*))
    in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvadd ~size) expr
  else if Z3.BitVector.is_bv_sub expr then
    let size =
      Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true (*ToDo*))
    in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvsub ~size) expr
  else if Z3.BitVector.is_bv_mul expr then
    let size =
      Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true (*ToDo*))
    in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvmult ~size) expr
  else if Z3.BitVector.is_bv_sdiv expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvdiv ~size) expr
  else if Z3.BitVector.is_bv_udiv expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), false) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvdiv ~size) expr
  else if Z3.BitVector.is_bv_smod expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvmod ~size) expr
  else if Z3.BitVector.is_bv_SRem expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvrem ~size) expr
  else if Z3.BitVector.is_bv_urem expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), false) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvrem ~size) expr
  else if Z3.BitVector.is_bv_shiftleft expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvshl ~size) expr
  else if Z3.BitVector.is_bv_shiftrightlogical expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvlshr ~size) expr
  else if Z3.BitVector.is_bv_shiftrightarithmetic expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvashr ~size) expr
  else if Z3.BitVector.is_bv_or expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvor ~size) expr
  else if Z3.BitVector.is_bv_and expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr), true) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvand ~size) expr
  else if Z3.Z3Array.is_store expr then
    match
      ( List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr,
        sort_of dtenv @@ Z3.Expr.get_sort expr )
    with
    | [ t1; t2; t3 ], T_array.SArray (s1, s2) -> T_array.mk_store s1 s2 t1 t2 t3
    | _ -> failwith "[z3:term_of]"
  else if Z3.Z3Array.is_constant_array expr then
    match
      ( List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr,
        sort_of dtenv @@ Z3.Expr.get_sort expr )
    with
    | [ t1 ], T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 t1
    | _ -> failwith "[z3:term_of]"
  else if Z3.Z3Array.is_select expr then
    let args = Z3.Expr.get_args expr in
    match (args, List.map ~f:(term_of ctx senv penv dtenv) args) with
    | [ e1; _e2 ], [ t1; t2 ] -> (
        match
          (T_array.eval_select t1 t2, sort_of dtenv @@ Z3.Expr.get_sort e1)
        with
        | Some te, _ -> te
        | _, T_array.SArray (s1, s2) -> T_array.mk_select s1 s2 t1 t2
        | _ -> failwith "[z3:term_of]")
    | _ -> failwith "[z3:term_of]"
  else if Z3.Seq.is_string ctx expr then
    T_string.make (Z3.Seq.get_string ctx expr)
  else if Z3.Seq.is_seq_sort ctx @@ Z3.Expr.get_sort expr then
    failwith "not supported"
  else if Z3.Seq.is_re_sort ctx @@ Z3.Expr.get_sort expr then
    failwith "not supported"
  else if Z3.AST.is_var @@ Z3.Expr.ast_of_expr expr then
    (* bound variables *)
    let _ =
      Debug.print @@ lazy ("[z3:term_of] bound var: " ^ Z3.Expr.to_string expr)
    in
    try
      let tvar, sort =
        List.nth_exn senv
        @@ List.length senv
           - Scanf.sscanf (Z3.Expr.to_string expr) "(:var %d)" Fn.id
           - 1
      in
      Debug.print
      @@ lazy
           ("[z3:term_of] identifier: " ^ Ident.name_of_tvar tvar ^ " : "
          ^ Term.str_of_sort sort);
      Term.mk_var tvar sort
    with _ ->
      failwith @@ "[z3:term_of] " ^ Z3.Expr.to_string expr ^ " not found"
    (*else if Z3.AST.is_quantifier @@ Z3.Expr.ast_of_expr expr then
      let q = Z3.Quantifier.quantifier_of_expr expr in
      let _ =
        if Z3.Quantifier.is_universal q then
          Debug.print @@ lazy ("universally quantified: " ^ Z3.Expr.to_string expr)
        else if Z3.Quantifier.is_existential q then
          Debug.print
          @@ lazy ("existentially quantified: " ^ Z3.Expr.to_string expr)
        else assert false
      in
      T_bool.of_formula @@ formula_of ctx senv penv dtenv expr*)
  else
    try
      (* function applications (and constants) *)
      let _ = Debug.print @@ lazy "function applications and constants" in
      let func =
        try Z3.Expr.get_func_decl expr
        with e ->
          Debug.print @@ lazy "get_func_decl failed";
          raise e
      in
      let name =
        Z3.FuncDecl.get_name func |> Z3.Symbol.get_string |> unescape_z3
        |> Str.split (Str.regexp divide_str)
        |> List.hd_exn
      in
      let ret_sort =
        try sort_of dtenv @@ Z3.FuncDecl.get_range func
        with Failure err ->
          Debug.print @@ lazy ("error: " ^ err);
          raise (Failure err)
      in
      let ts =
        List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr
      in
      let arg_sorts = List.map ~f:Term.sort_of ts in
      (* the following causes an exception if [expr] contains a bound variable:
         let arg_sorts =
          List.map ~f:(Expr.get_sort >> sort_of dtenv) @@ Z3.Expr.get_args expr
         in *)
      if String.(name = "mp" || name = "hyper-res" || name = "asserted") then
        Term.mk_fvar_app (Ident.Tvar name) (arg_sorts @ [ ret_sort ]) ts
      else
        try
          (* algebraic data types *)
          Debug.print @@ lazy "algebraic data types";
          match look_up_func dtenv func with
          | Some (dt, `Cons cons) ->
              Debug.print @@ lazy "constructor";
              T_dt.mk_cons dt (Datatype.name_of_cons cons) ts
          | Some (dt, `IsCons cons) ->
              Debug.print @@ lazy "tester";
              T_bool.of_atom
              @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons)
              @@ List.hd_exn ts
          | Some (dt, `Sel sel) ->
              Debug.print @@ lazy "accessor";
              T_dt.mk_sel dt (Datatype.name_of_sel sel) @@ List.hd_exn ts
          | None when T_dt.is_sdt ret_sort && List.is_empty ts ->
              Debug.print @@ lazy "no definition";
              Term.mk_var (Ident.Tvar name) ret_sort
          | _ -> failwith "[z3:term_of] not an ADT term"
        with Failure err -> (
          Debug.print @@ lazy ("error: " ^ err);
          try
            (* tuples *)
            if String.is_prefix ~prefix:unint_tuple_prefix name then
              T_tuple.mk_tuple_cons arg_sorts ts
            else if
              String.is_prefix ~prefix:unint_tuple_sel_prefix name
              && List.length ts = 1
            then
              let pre_length = String.length unint_tuple_sel_prefix in
              let i =
                Int.of_string
                @@ String.sub name ~pos:pre_length
                     ~len:(String.length name - pre_length)
              in
              match (ts, arg_sorts) with
              | [ t ], [ T_tuple.STuple elem_sorts ] ->
                  T_tuple.mk_tuple_sel elem_sorts t i
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if
              String.(
                name
                = "is" (*ToDo: Z3 automatically generates a tester of the name*))
              && List.length ts = 1
            then
              match (ts, arg_sorts) with
              | [ _t ], [ T_tuple.STuple _elem_sorts ] ->
                  (*ToDo*)
                  T_bool.mk_true
                    () (*T_bool.of_atom @@ T_tuple.mk_is_tuple elem_sorts t*)
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.(name = unint_epsilon) && List.is_empty ts then
              T_sequence.mk_eps ()
            else if
              String.is_prefix ~prefix:unint_symbol_prefix name
              && List.is_empty ts
            then
              let pre_length = String.length unint_symbol_prefix in
              let symbol =
                String.sub name ~pos:pre_length
                  ~len:(String.length name - pre_length)
              in
              T_sequence.mk_symbol symbol
            else if String.(name = unint_concat_fin) then
              match ts with
              | [ t1; t2 ] -> T_sequence.mk_concat ~fin:true t1 t2
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.(name = unint_concat_inf) && List.length ts = 2 then
              match ts with
              | [ t1; t2 ] -> T_sequence.mk_concat ~fin:false t1 t2
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.is_prefix ~prefix:unint_is_prefix_of_fin name then
              match ts with
              | [ t1; t2 ] ->
                  T_bool.of_atom @@ T_sequence.mk_is_prefix true t1 t2
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if
              String.is_prefix ~prefix:unint_is_prefix_of_inf name
              && List.length ts = 2
            then
              match ts with
              | [ t1; t2 ] ->
                  T_bool.of_atom @@ T_sequence.mk_is_prefix false t1 t2
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.is_prefix ~prefix:unint_is_in_reg_exp_fin_prefix name
            then
              let regexp = failwith "not supported" in
              match ts with
              | [ t ] ->
                  T_bool.of_atom @@ T_sequence.mk_is_in_regexp true regexp t
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.is_prefix ~prefix:unint_is_in_reg_exp_inf_prefix name
            then
              let regexp = failwith "not supported" in
              match ts with
              | [ t ] ->
                  T_bool.of_atom @@ T_sequence.mk_is_in_regexp false regexp t
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else failwith "[z3:term_of] not a tuple/sequence term"
          with Failure err -> (
            Debug.print @@ lazy ("error: " ^ err);
            (* function applications *)
            match Map.Poly.find (get_fenv ()) (Ident.Tvar name) with
            | Some (params, sret, _, _, _) ->
                Term.mk_fvar_app (Ident.Tvar name)
                  (List.map params ~f:snd @ [ sret ] (*arg_sorts @ [ret_sort]*))
                  ts
            | _ -> (
                try
                  (* formulas *)
                  match sort_of dtenv @@ Z3.Expr.get_sort expr with
                  | T_bool.SBool ->
                      if List.is_empty ts then
                        Term.mk_var (Ident.Tvar name) T_bool.SBool
                      else
                        T_bool.of_formula @@ formula_of ctx senv penv dtenv expr
                  | _ -> failwith "[z3:term_of] not a formula"
                with Failure err ->
                  Debug.print @@ lazy ("error: " ^ err);
                  (* variables / function variable applications *)
                  if List.is_empty ts then
                    Term.mk_var (Ident.Tvar name) ret_sort
                  else
                    Term.mk_fvar_app (Ident.Tvar name)
                      (arg_sorts @ [ ret_sort ]) ts)))
    with _ -> T_bool.of_formula @@ formula_of ctx senv penv dtenv expr

and (* Conversion from Z3 expressions to atoms *)
    atom_of ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  Debug.print @@ lazy ("[z3:atom_of] " ^ Z3.Expr.to_string expr);
  if Z3.Boolean.is_true expr then Atom.mk_true ()
  else if Z3.Boolean.is_false expr then Atom.mk_false ()
  else if Z3.Boolean.is_eq expr then
    match Z3.Expr.get_args expr with
    | [ e1; e2 ]
      when Stdlib.(Term.is_bool_sort @@ sort_of dtenv @@ Z3.Expr.get_sort e1) ->
        T_bool.mk_eq
          (T_bool.of_formula @@ formula_of ctx senv penv dtenv e1)
          (T_bool.of_formula @@ formula_of ctx senv penv dtenv e2)
    | _ -> apply_brel ctx senv penv dtenv T_bool.mk_eq expr
  else if Z3.Arithmetic.is_real_is_int expr then
    apply_urel ctx senv penv dtenv T_irb.mk_is_int expr
  else if Z3.Arithmetic.is_le expr then
    Typeinf.typeinf_atom ~print:Debug.print
    @@ apply_brel ctx senv penv dtenv T_num.mk_nleq expr
  else if Z3.Arithmetic.is_ge expr then
    Typeinf.typeinf_atom ~print:Debug.print
    @@ apply_brel ctx senv penv dtenv T_num.mk_ngeq expr
  else if Z3.Arithmetic.is_lt expr then
    Typeinf.typeinf_atom ~print:Debug.print
    @@ apply_brel ctx senv penv dtenv T_num.mk_nlt expr
  else if Z3.Arithmetic.is_gt expr then
    Typeinf.typeinf_atom ~print:Debug.print
    @@ apply_brel ctx senv penv dtenv T_num.mk_ngt expr
  else if Z3.BitVector.is_bv_sle expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), true)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvleq ~size) expr
  else if Z3.BitVector.is_bv_ule expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), false)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvleq ~size) expr
  else if Z3.BitVector.is_bv_sge expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), true)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgeq ~size) expr
  else if Z3.BitVector.is_bv_uge expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), false)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgeq ~size) expr
  else if Z3.BitVector.is_bv_slt expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), true)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvlt ~size) expr
  else if Z3.BitVector.is_bv_ult expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), false)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvlt ~size) expr
  else if Z3.BitVector.is_bv_sgt expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), true)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgt ~size) expr
  else if Z3.BitVector.is_bv_ugt expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e), false)
      | _ -> failwith "[z3:atom_of]"
    in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgt ~size) expr
  else if Z3.AST.is_var @@ Z3.Expr.ast_of_expr expr then
    (* bound variables *)
    let _ =
      Debug.print @@ lazy ("[z3:atom_of] bound var: " ^ Z3.Expr.to_string expr)
    in
    try
      let tvar, _sort (* assume bool*) =
        List.nth_exn senv
        @@ List.length senv
           - Scanf.sscanf (Z3.Expr.to_string expr) "(:var %d)" Fn.id
           - 1
      in
      Debug.print @@ lazy ("[z3:atom_of] identifier: " ^ Ident.name_of_tvar tvar);
      match
        List.Assoc.find ~equal:Stdlib.( = ) penv (Ident.tvar_to_pvar tvar)
      with
      | Some _ -> Atom.mk_pvar_app (Ident.tvar_to_pvar tvar) [] [] (*ToDo*)
      | _ -> Atom.of_bool_term @@ Term.mk_var tvar T_bool.SBool
    with _ ->
      failwith @@ "[z3:atom_of] " ^ Z3.Expr.to_string expr ^ " not found"
  else
    let func = Z3.Expr.get_func_decl expr in
    let name =
      Z3.FuncDecl.get_name func |> Z3.Symbol.get_string |> unescape_z3
      |> Str.split (Str.regexp divide_str)
      |> List.hd_exn
    in
    let pvar = Ident.Pvar name in
    let atm =
      let ts =
        List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr
      in
      let sorts = List.map ts ~f:Term.sort_of in
      Atom.mk_pvar_app pvar sorts ts
    in
    if String.is_prefix name ~prefix:"query!" then (*ToDo*)
      atm
    else
      match List.Assoc.find ~equal:Stdlib.( = ) penv pvar with
      | Some _ -> atm
      | None -> (
          (*print_endline @@ name ^ " is not bound in the environment";*)
          try Atom.of_bool_term @@ term_of ctx senv penv dtenv expr
          with Failure err ->
            failwith
            @@ sprintf "[z3:atom_of] %s caused %s" (Z3.Expr.to_string expr) err)

and (* Conversion from Z3 expressions to formulas *)
    formula_of ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  Debug.print @@ lazy ("[z3:formula_of] " ^ Z3.Expr.to_string expr);
  if Z3.Boolean.is_not expr then
    match Z3.Expr.get_args expr with
    | [ body ] -> Formula.negate (formula_of ctx senv penv dtenv body)
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_and expr then
    Formula.and_of
    @@ List.map ~f:(formula_of ctx senv penv dtenv)
    @@ Z3.Expr.get_args expr
  else if Z3.Boolean.is_or expr then
    Formula.or_of
    @@ List.map ~f:(formula_of ctx senv penv dtenv)
    @@ Z3.Expr.get_args expr
  else if Z3.Boolean.is_iff expr then
    Z3.Expr.get_args expr |> List.map ~f:(formula_of ctx senv penv dtenv)
    |> function
    | [ phi1; phi2 ] -> Formula.mk_iff phi1 phi2
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_implies expr then
    Z3.Expr.get_args expr |> List.map ~f:(formula_of ctx senv penv dtenv)
    |> function
    | [ phi1; phi2 ] -> Formula.mk_imply phi1 phi2
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_ite expr then
    match Z3.Expr.get_args expr with
    | [ e1; e2; e3 ] ->
        Formula.of_bool_term
        @@ T_bool.ifte
             (formula_of ctx senv penv dtenv e1)
             (term_of ctx senv penv dtenv e2)
             (term_of ctx senv penv dtenv e3)
    | _ -> failwith "[z3:formula_of]"
  else if Z3.AST.is_quantifier @@ Z3.Expr.ast_of_expr expr then
    let q = Z3.Quantifier.quantifier_of_expr expr in
    let binder =
      if Z3.Quantifier.is_universal q then Formula.Forall
      else if Z3.Quantifier.is_existential q then Formula.Exists
      else assert false
    in
    let bounds =
      List.zip_exn
        (List.map ~f:(fun x ->
             if true (*ToDo*) then
               Ident.mk_fresh_tvar
                 ~prefix:(Some (Z3.Symbol.get_string x ^ "_"))
                 ()
             else Ident.Tvar (Z3.Symbol.get_string x))
        @@ Z3.Quantifier.get_bound_variable_names q)
        (List.map ~f:(sort_of dtenv) @@ Z3.Quantifier.get_bound_variable_sorts q)
    in
    let senv = senv @ bounds in
    Formula.mk_bind binder bounds
    @@ formula_of ctx senv penv dtenv
    @@ Z3.Quantifier.get_body q
  else Formula.mk_atom @@ atom_of ctx senv penv dtenv expr

let dummy_term_map_of terms =
  Map.of_set_exn
  @@ Set.Poly.filter_map terms ~f:(function
       | tvar, (T_dt.SUS (name, _) as sort) ->
           let tvar' = Ident.mk_fresh_dummy_tvar name in
           LogicOld.add_dummy_term tvar' sort;
           Some (tvar, Term.mk_var tvar' sort)
       | _ -> None)

let add_dummy_term model =
  List.filter_map model ~f:(function _, Some t -> Some t | _ -> None)
  |> List.fold_left ~init:Set.Poly.empty ~f:(fun ret term ->
         Set.filter ~f:(function _, T_dt.SUS _ -> true | _ -> false)
         @@ Set.union ret @@ Term.term_sort_env_of term)
  |> Set.iter ~f:(uncurry2 add_dummy_term)

let model_of ctx dtenv model =
  try
    let model =
      List.map
        (try Z3.Model.get_decls model
         with _ ->
           (*print_endline "get_decls error";*)
           Z3.Model.get_func_decls model @ Z3.Model.get_const_decls model)
        ~f:(fun decl ->
          let x =
            Z3.FuncDecl.get_name decl |> Z3.Symbol.get_string
            |> Str.split (Str.regexp divide_str)
            |> List.hd_exn
          in
          let s =
            Sort.mk_fun
            @@ List.map ~f:(sort_of dtenv)
            @@ Z3.FuncDecl.get_domain decl
            @ [ Z3.FuncDecl.get_range decl ]
          in
          ( (Ident.Tvar x, s),
            if Z3.FuncDecl.get_arity decl = 0 then
              match Z3.Model.get_const_interp model decl with
              | Some expr -> Some (term_of ctx [] [] dtenv expr)
              | None -> None
            else
              match Z3.Model.get_func_interp model decl with
              | Some _func -> None (*ToDo*)
              | None -> None ))
    in
    Debug.print @@ lazy ("model is: " ^ str_of_model model);
    model
  with _ ->
    (*print_endline "get_func_decls or get_const_decls error";*)
    [] (*ToDo*)

(** encoding *)

let of_var ctx (Ident.Tvar var) = Z3.Symbol.mk_string ctx @@ String.escaped var
let list_type s ctx = Z3.Z3List.mk_sort ctx (Z3.Symbol.mk_string ctx "list") s
let array_type t1 t2 ctx = Z3.Z3Array.mk_sort ctx t1 t2
let sorts_of_tuple sort = sort |> Z3.Tuple.get_mk_decl |> Z3.FuncDecl.get_domain

(* Conversion from sorts to Z3 sorts *)

let str_of_z3_env env =
  Set.fold ~init:"z3_env:" env ~f:(fun ret (dt, sort) ->
      sprintf "%s\nLogicOld: %s\nZ3: %s\n%s\n%s" ret (Datatype.str_of dt)
        (Z3.Sort.to_string sort)
        (String.concat ~sep:"\n"
        @@ List.map2_exn (Z3.Datatype.get_constructors sort)
             (Z3.Datatype.get_accessors sort) ~f:(fun cons sels ->
               String.concat ~sep:"\n"
               @@ sprintf "(#%d) %s" (Z3.FuncDecl.get_id cons)
                    (Z3.FuncDecl.to_string cons)
                  :: List.map sels ~f:(fun sel ->
                         sprintf "(#%d) %s" (Z3.FuncDecl.get_id sel)
                           (Z3.FuncDecl.to_string sel))))
        (String.concat ~sep:"\n"
        @@ List.map (Z3.Datatype.get_recognizers sort) ~f:(fun iscons ->
               sprintf "(#%d) %s"
                 (Z3.FuncDecl.get_id iscons)
                 (Z3.FuncDecl.to_string iscons))))

let rec of_sort ctx dtenv = function
  | Sort.SVar (Ident.Svar svar) ->
      Z3.Sort.mk_uninterpreted_s ctx @@ unint_svar_prefix ^ svar
  (*| Sort.SArrow (s1, (s2, Sort.Pure)) ->
    Z3Array.mk_sort ctx (of_sort ctx dtenv s1) (of_sort ctx dtenv s2)*)
  | Sort.SArrow (_, _) as s ->
      Z3.Sort.mk_uninterpreted_s ctx @@ unint_arrow_prefix ^ Term.str_of_sort s
  | T_bool.SBool -> Z3.Boolean.mk_sort ctx
  | T_int.SInt -> Z3.Arithmetic.Integer.mk_sort ctx
  | T_real.SReal -> Z3.Arithmetic.Real.mk_sort ctx
  | T_bv.SBV size -> Z3.BitVector.mk_sort ctx (T_bv.bits_of size)
  | T_tuple.STuple sorts -> tuple_sort_of ctx dtenv sorts
  | T_dt.SUS (name, []) -> Z3.Sort.mk_uninterpreted_s ctx name
  | T_dt.SUS (name, params) ->
      if true then Z3.Sort.mk_uninterpreted_s ctx unint_unsupported
      else
        Z3.Sort.mk_uninterpreted_s ctx
        @@
        if true then name ^ "_with_args"
        else
          sprintf "(%s) %s"
            (String.concat_map_list ~sep:"," params ~f:Term.str_of_sort)
            name
  | T_dt.SDT dt -> (
      let name = Datatype.full_name_of dt in
      match
        Set.find dtenv ~f:(fst >> Datatype.full_name_of >> String.( = ) name)
      with
      | Some (_, sort) -> sort
      | None ->
          Debug.print
          @@ lazy
               (sprintf "[z3:of_sort] adding %s to %s"
                  (Term.str_of_sort @@ T_dt.SDT dt)
                  (str_of_z3_env dtenv));
          of_sort ctx (update_z3env ctx dtenv dt) (T_dt.SDT dt))
  | T_array.SArray (si, se) ->
      Z3.Z3Array.mk_sort ctx (of_sort ctx dtenv si) (of_sort ctx dtenv se)
  | T_sequence.SSequence fin ->
      Z3.Sort.mk_uninterpreted_s ctx
        (if fin then unint_finseq else unint_infseq)
  | T_string.SString -> Z3.Seq.mk_string_sort ctx
  | T_regex.SRegEx -> Z3.Seq.mk_re_sort ctx @@ Z3.Seq.mk_string_sort ctx
  | sort ->
      failwith @@ sprintf "[z3:of_sort] %s is unknown" @@ Term.str_of_sort sort

and tuple_sort_of ctx dtenv sorts =
  let tuple_num = List.length sorts in
  Z3.Tuple.mk_sort ctx
    (Z3.Symbol.mk_string ctx
    @@ sprintf "%s(%s)" unint_tuple_prefix
    (*tuple_num*)
    @@ String.concat_map_list ~sep:"," ~f:Term.short_name_of_sort sorts)
    (* (tuple_prefix ^ string_of_int tuple_num |> Idnt.make |> sym_of_var) *)
    (List.init tuple_num ~f:(fun i ->
         Z3.Symbol.mk_string ctx @@ unint_tuple_sel_prefix ^ string_of_int i))
    (List.map sorts ~f:(of_sort ctx dtenv))

and update_z3env ctx dtenv t =
  match Datatype.flag_of t with
  | Undef ->
      Set.add dtenv (t, Z3.Sort.mk_uninterpreted_s ctx (Datatype.name_of t))
  | Alias _ | FCodt -> failwith "not supported"
  | FDt ->
      let dts =
        List.filter_map (Datatype.full_dts_of t) ~f:(fun dt ->
            if List.is_empty @@ Datatype.conses_of_dt dt then None else Some dt)
      in
      let sorts =
        uncurry2 (Z3.Datatype.mk_sorts_s ctx)
        @@ List.unzip
        @@ List.map dts ~f:(fun dt ->
               let dt_name = Datatype.full_name_of_dt dt in
               ( dt_name,
                 List.map (Datatype.conses_of_dt dt) ~f:(fun cons ->
                     let name = Datatype.name_of_cons cons in
                     Debug.print
                     @@ lazy
                          (sprintf "[update_z3env] %s constructor: %s" dt_name
                             name);
                     let is_cons_name =
                       Z3.Symbol.mk_string ctx @@ unint_is_cons_prefix ^ name
                     in
                     Debug.print
                     @@ lazy
                          (sprintf "[update_z3env] %s tester: %s" dt_name
                          @@ Z3.Symbol.get_string is_cons_name);
                     let sels_names, ret_sorts, ref_sorts =
                       List.fold_left (Datatype.sels_of_cons cons)
                         ~init:([], [], [])
                         ~f:(fun (sels_names, ret_sorts, ref_sorts) -> function
                         | Datatype.Sel (name, ret_sort) ->
                             Debug.print
                             @@ lazy
                                  (sprintf "[update_z3env] %s accessor: %s"
                                     dt_name name);
                             ( Z3.Symbol.mk_string ctx name :: sels_names,
                               Some (of_sort ctx dtenv ret_sort) :: ret_sorts,
                               0 :: ref_sorts )
                         | Datatype.InSel (name, ret_name, args) -> (
                             Debug.print
                             @@ lazy
                                  (sprintf "[update_z3env] %s rec. accessor: %s"
                                     dt_name name);
                             let full_name =
                               Datatype.full_name_of
                                 (Datatype.make ret_name
                                    [ Datatype.mk_dt ret_name args ]
                                    FDt)
                             in
                             match
                               Set.find dtenv
                                 ~f:
                                   (fst >> Datatype.full_name_of
                                  >> String.( = ) full_name)
                             with
                             | Some (_, sort) ->
                                 ( Z3.Symbol.mk_string ctx name :: sels_names,
                                   Some sort :: ret_sorts,
                                   0 :: ref_sorts )
                             | None -> (
                                 match
                                   List.findi dts ~f:(fun _ ->
                                       Datatype.name_of_dt
                                       >> String.( = ) ret_name)
                                 with
                                 | Some (i, _) ->
                                     (* Debug.print @@ lazy (sprintf "ref id:%d" i); *)
                                     ( Z3.Symbol.mk_string ctx name :: sels_names,
                                       None :: ret_sorts,
                                       i :: ref_sorts )
                                 | _ -> assert false)))
                     in
                     let z3cons =
                       Z3.Datatype.mk_constructor ctx
                         (Z3.Symbol.mk_string ctx name)
                         is_cons_name (List.rev sels_names) (List.rev ret_sorts)
                         (List.rev ref_sorts)
                     in
                     if false then (
                       Debug.print
                       @@ lazy
                            ("z3 tester: " ^ Z3.FuncDecl.to_string
                            @@ Z3.Datatype.Constructor.get_tester_decl z3cons);
                       List.iter
                         (Z3.Datatype.Constructor.get_accessor_decls z3cons)
                         ~f:(fun sel ->
                           Debug.print
                           @@ lazy ("z3 sel:" ^ Z3.FuncDecl.to_string sel)));
                     z3cons) ))
      in
      List.fold2_exn dts sorts ~init:dtenv ~f:(fun dtenv dt sort ->
          Set.add dtenv
            ( Datatype.update_name (Datatype.update_dts t dts)
              @@ Datatype.name_of_dt dt,
              sort ))

and z3_dtenv_of_dtenv ?(init = Set.Poly.empty) ctx dtenv =
  (* Debug.print @@ lazy (sprintf "mk z3 dtenv from:\n%s" @@ DTEnv.str_of dtenv); *)
  let z3_dtenv =
    Map.Poly.fold dtenv ~init ~f:(fun ~key:_ ~data env ->
        (* Debug.print @@ lazy (sprintf "mk sort:%s \n%s" key (Datatype.str_of data)); *)
        let name = Datatype.full_name_of data in
        if Set.exists env ~f:(fst >> Datatype.full_name_of >> String.( = ) name)
        then env
        else update_z3env ctx env data)
  in
  (* Debug.print @@ lazy (str_of_z3_env z3_dtenv); *)
  z3_dtenv

let z3_dtenv_of_formula ?(init = Set.Poly.empty) ctx phi =
  update_dtenv @@ DTEnv.of_formula phi;
  Debug.print
  @@ lazy (sprintf "[z3_dtenv_of] from:\n%s" @@ DTEnv.str_of @@ get_dtenv ());
  z3_dtenv_of_dtenv ~init ctx @@ get_dtenv ()

let z3_dt_of (dtenv : dtenv) dt =
  try
    snd
    @@ Set.find_exn dtenv
         ~f:
           (fst >> Datatype.full_name_of
           >> (*(fun name -> print_endline name; name)*)
           String.( = ) (Datatype.full_name_of dt))
  with _ ->
    failwith @@ sprintf "[z3_dt_of] %s not found" (Datatype.full_name_of dt)

let z3_cons_of (dtenv : dtenv) dt name =
  let z3_conses = Z3.Datatype.get_constructors @@ z3_dt_of dtenv dt in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_conses) ~f:(fun (cons, z3_cons) ->
      if String.(Datatype.name_of_cons cons = name) then Some z3_cons else None)

let z3_sel_of (dtenv : dtenv) dt name =
  let z3_selss = Z3.Datatype.get_accessors @@ z3_dt_of dtenv dt in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_selss) ~f:(fun (cons, z3_sels) ->
      let sels = Datatype.sels_of_cons cons in
      List.find_map (List.zip_exn sels z3_sels) ~f:(fun (sel, z3_sel) ->
          if String.(name = Datatype.name_of_sel sel) then Some z3_sel else None))

let z3_iscons_of (dtenv : dtenv) dt name =
  let z3_testers = Z3.Datatype.get_recognizers @@ z3_dt_of dtenv dt in
  let conses = Datatype.conses_of dt in
  List.find_map_exn (List.zip_exn conses z3_testers)
    ~f:(fun (cons, z3_tester) ->
      if String.(Datatype.name_of_cons cons = name) then Some z3_tester
      else None)

let z3_epsilon ctx =
  Z3.FuncDecl.mk_func_decl_s ctx unint_epsilon []
  @@ Z3.Sort.mk_uninterpreted_s ctx unint_finseq

let z3_symbol_of ctx str =
  Z3.FuncDecl.mk_func_decl_s ctx
    (unint_symbol_prefix ^ str (*ToDo: need to avoid escaping by z3?*))
    []
  @@ Z3.Sort.mk_uninterpreted_s ctx unint_finseq

let z3_concat ctx fin =
  let sort =
    if fin then Z3.Sort.mk_uninterpreted_s ctx unint_finseq
    else Z3.Sort.mk_uninterpreted_s ctx unint_infseq
  in
  Z3.FuncDecl.mk_func_decl_s ctx
    (if fin then unint_concat_fin else unint_concat_inf)
    [ Z3.Sort.mk_uninterpreted_s ctx unint_finseq; sort ]
    sort

let z3_is_prefix_of ctx fin =
  Z3.FuncDecl.mk_func_decl_s ctx
    (if fin then unint_is_prefix_of_fin else unint_is_prefix_of_inf)
    [
      Z3.Sort.mk_uninterpreted_s ctx unint_finseq;
      (Z3.Sort.mk_uninterpreted_s ctx
      @@ if fin then unint_finseq else unint_infseq);
    ]
    (Z3.Boolean.mk_sort ctx)

let z3_is_in_reg_exp ctx fin regexp =
  Z3.FuncDecl.mk_func_decl_s ctx
    ((if fin then unint_is_in_reg_exp_fin_prefix
      else unint_is_in_reg_exp_inf_prefix)
    ^ String.paren
    @@ Grammar.RegWordExp.str_of Fn.id regexp)
    [
      (Z3.Sort.mk_uninterpreted_s ctx
      @@ if fin then unint_finseq else unint_infseq);
    ]
    (Z3.Boolean.mk_sort ctx)

let pred_decl_of ctx dtenv (pvar, sorts) =
  ( pvar,
    Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_pvar pvar)
      (List.map sorts ~f:(of_sort ctx dtenv))
      (Z3.Boolean.mk_sort ctx) )

(* Conversion from formulas to Z3 expressions *)
let rec of_formula_aux ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) phi =
  if false then Debug.print @@ lazy ("[z3:of_formula_aux] " ^ Formula.str_of phi);
  match phi with
  | Formula.Atom ((Atom.App (Predicate.Var (pvar, sorts), _, _) as atom), _) ->
      let penv' =
        if not @@ List.Assoc.mem ~equal:Stdlib.( = ) penv pvar then
          pred_decl_of ctx dtenv (pvar, sorts) :: penv
        else penv
      in
      of_atom ~id ctx env penv' fenv dtenv atom
  | Formula.Atom (atom, _) -> of_atom ~id ctx env penv fenv dtenv atom
  | Formula.UnaryOp (Not, phi1, _) ->
      Z3.Boolean.mk_not ctx @@ of_formula_aux ~id ctx env penv fenv dtenv phi1
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      Z3.Boolean.mk_and ctx
        [
          of_formula_aux ~id ctx env penv fenv dtenv phi1;
          of_formula_aux ~id ctx env penv fenv dtenv phi2;
        ]
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      Z3.Boolean.mk_or ctx
        [
          of_formula_aux ~id ctx env penv fenv dtenv phi1;
          of_formula_aux ~id ctx env penv fenv dtenv phi2;
        ]
  | Formula.BinaryOp (Iff, phi1, phi2, _) ->
      Z3.Boolean.mk_iff ctx
        (of_formula_aux ~id ctx env penv fenv dtenv phi1)
        (of_formula_aux ~id ctx env penv fenv dtenv phi2)
  | Formula.BinaryOp (Xor, phi1, phi2, _) ->
      Z3.Boolean.mk_xor ctx
        (of_formula_aux ~id ctx env penv fenv dtenv phi1)
        (of_formula_aux ~id ctx env penv fenv dtenv phi2)
  | Formula.BinaryOp (Imply, phi1, phi2, _) ->
      Z3.Boolean.mk_implies ctx
        (of_formula_aux ~id ctx env penv fenv dtenv phi1)
        (of_formula_aux ~id ctx env penv fenv dtenv phi2)
  | Formula.Bind (binder, bounds, body, _) ->
      let vars = List.map bounds ~f:(fst >> of_var ctx) in
      let sorts = List.map bounds ~f:(snd >> of_sort ctx dtenv) in
      let env = List.rev bounds @ env in
      let body = of_formula_aux ~id ctx env penv fenv dtenv body in
      Z3.Quantifier.expr_of_quantifier
      @@ (match binder with
         | Formula.Forall -> Z3.Quantifier.mk_forall
         | Formula.Exists -> Z3.Quantifier.mk_exists
         | _ ->
             failwith
             @@ "[z3:of_formula_aux] Z3 does not support random quantifiers")
           ctx sorts vars body None [] [] None None
  | Formula.LetRec ([], phi, _) ->
      of_formula_aux ~id ctx env penv fenv dtenv phi
  | Formula.LetRec (_, _, _) ->
      failwith @@ "[z3:of_formula_aux] Z3 does not support fixpoint predicates"
  | Formula.LetFormula (_, _, _, _, _) ->
      failwith @@ "[z3:of_formula_aux] let-expressions not supported"

and of_var_term ~id ctx env dtenv t =
  let (var, sort), _ = Term.let_var t in
  if false then
    Debug.print
    @@ lazy
         (sprintf "[z3:of_var_term] %s : %s" (Ident.name_of_tvar var)
            (Term.str_of_sort sort));
  match List.findi env ~f:(fun _ (key, _) -> Stdlib.(key = var)) with
  | Some (i, (_, sort')) ->
      if
        match (sort, sort') with
        | T_bv.SBV None, T_bv.SBV _ | T_bv.SBV _, T_bv.SBV None -> false
        | _ -> Stdlib.(sort <> sort')
      then
        failwith
        @@ sprintf "%s is assigned inconsistent types %s and %s"
             (Ident.name_of_tvar var) (Term.str_of_sort sort)
             (Term.str_of_sort sort');
      (* Debug.print @@ lazy ("[z3:of_var_term] mk quantifier"); *)
      (* lock (); (fun ret -> unlock (); ret) @@   *)
      Z3.Quantifier.mk_bound ctx i @@ of_sort ctx dtenv sort
  | None ->
      let name = Ident.name_of_tvar var in
      (* Debug.print @@ lazy ("[z3:of_var_term] mk const var " ^ name ^ " : " ^ Term.str_of_sort sort); *)
      let symbol =
        of_var ctx
        @@
        match id with
        | None -> var
        | Some id ->
            Ident.Tvar
              (sprintf "%s%s%d%s" name divide_str id
                 (Term.short_name_of_sort sort))
      in
      Z3.Expr.mk_const ctx symbol @@ of_sort ctx dtenv sort

(* Conversion from terms to Z3 expressions *)
and of_term ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) t =
  if false then Debug.print @@ lazy (sprintf "[z3:of_term] %s" @@ Term.str_of t);
  match t with
  | Term.Var _ -> of_var_term ~id ctx env dtenv t
  | LetTerm (_, _, _, _, _) ->
      failwith @@ "[z3:of_term] not supported: " ^ Term.str_of t
  | FunApp (fsym, args, _) -> (
      match (fsym, List.map ~f:(of_term ~id ctx env penv fenv dtenv) args) with
      | T_bool.Formula phi, [] -> of_formula_aux ~id ctx env penv fenv dtenv phi
      | T_bool.IfThenElse, [ cond; then_; else_ ] ->
          Z3.Boolean.mk_ite ctx cond then_ else_
      | T_int.Int n, [] ->
          Z3.Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n)
      | T_real.Real r, [] -> (
          match Q.classify r with
          | Q.ZERO | Q.NZERO -> (
              try Z3.Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
              with _ -> failwith @@ Q.to_string r ^ " cannot be parsed")
          | Q.UNDEF ->
              Z3.Arithmetic.mk_div ctx
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
          | Q.INF ->
              Z3.Arithmetic.mk_div ctx
                (Z3.Arithmetic.Real.mk_numeral_i ctx 1)
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
          | Q.MINF ->
              Z3.Arithmetic.mk_div ctx
                (Z3.Arithmetic.Real.mk_numeral_i ctx (-1))
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0))
      | T_real.Alge _, [ _ ] ->
          Z3.Arithmetic.Real.mk_numeral_s ctx @@ Term.str_of t (*ToDo*)
      | T_bv.BVNum (size, n), [] ->
          Z3.BitVector.mk_numeral ctx (Z.to_string n) (T_bv.bits_of size)
      | (T_int.Neg | T_real.RNeg), [ n ] ->
          if Z3.Expr.is_const n then (*ToDo*) Z3.Arithmetic.mk_unary_minus ctx n
          else Z3.Arithmetic.mk_unary_minus ctx n
      | T_bv.BVNeg _size, [ n ] -> Z3.BitVector.mk_neg ctx n
      | ((T_int.Abs | T_real.RAbs) as op), [ n ] ->
          (*ToDo*)
          let is_minus =
            Z3.Arithmetic.mk_lt ctx n
              (match op with
              | T_int.Abs -> Z3.Arithmetic.Integer.mk_numeral_i ctx 0
              | T_real.RAbs -> Z3.Arithmetic.Real.mk_numeral_i ctx 0
              | _ -> assert false)
          in
          let minus_n =
            of_term ~id ctx env penv fenv dtenv
              (T_int.mk_neg @@ List.hd_exn args)
          in
          Z3.Boolean.mk_ite ctx is_minus minus_n n
      | (T_int.Add | T_real.RAdd), [ t1; t2 ] ->
          Z3.Arithmetic.mk_add ctx [ t1; t2 ]
      | T_bv.BVAdd _size, [ t1; t2 ] -> Z3.BitVector.mk_add ctx t1 t2
      | (T_int.Sub | T_real.RSub), [ t1; t2 ] ->
          Z3.Arithmetic.mk_sub ctx [ t1; t2 ]
      | T_bv.BVSub _size, [ t1; t2 ] -> Z3.BitVector.mk_sub ctx t1 t2
      | (T_int.Mult | T_real.RMult), [ t1; t2 ] ->
          Z3.Arithmetic.mk_mul ctx [ t1; t2 ]
      | T_bv.BVMult _size, [ t1; t2 ] -> Z3.BitVector.mk_mul ctx t1 t2
      | T_int.Div, [ t1; t2 ] -> Z3.Arithmetic.mk_div ctx t1 t2
      | T_real.RDiv, [ t1; t2 ] ->
          (*ToDo: necessary? *)
          Z3.Arithmetic.mk_div ctx
            (if Z3.Arithmetic.is_int t1 then
               Z3.Arithmetic.Integer.mk_int2real ctx t1
             else t1)
            (if Z3.Arithmetic.is_int t2 then
               Z3.Arithmetic.Integer.mk_int2real ctx t2
             else t2)
      | T_bv.BVDiv size, [ t1; t2 ] ->
          (if T_bv.signed_of size then Z3.BitVector.mk_sdiv
           else Z3.BitVector.mk_udiv)
            ctx t1 t2
      | T_int.Mod, [ t1; t2 ] -> Z3.Arithmetic.Integer.mk_mod ctx t1 t2
      | T_bv.BVMod size, [ t1; t2 ] ->
          assert (T_bv.signed_of size);
          Z3.BitVector.mk_smod ctx t1 t2
      | T_int.Rem, [ t1; t2 ] -> Z3.Arithmetic.Integer.mk_rem ctx t1 t2
      | T_bv.BVRem size, [ t1; t2 ] ->
          (if T_bv.signed_of size then Z3.BitVector.mk_srem
           else Z3.BitVector.mk_urem)
            ctx t1 t2
      | (T_int.Power | T_real.RPower), [ t1; t2 ] ->
          Z3.Arithmetic.mk_power ctx t1 t2
      | T_bv.BVSHL _size, [ t1; t2 ] -> Z3.BitVector.mk_shl ctx t1 t2
      | T_bv.BVLSHR _size, [ t1; t2 ] -> Z3.BitVector.mk_lshr ctx t1 t2
      | T_bv.BVASHR _size, [ t1; t2 ] -> Z3.BitVector.mk_ashr ctx t1 t2
      | T_bv.BVOr _size, [ t1; t2 ] -> Z3.BitVector.mk_or ctx t1 t2
      | T_bv.BVAnd _size, [ t1; t2 ] -> Z3.BitVector.mk_and ctx t1 t2
      | T_irb.IntToReal, [ t ] -> Z3.Arithmetic.Integer.mk_int2real ctx t
      | T_irb.RealToInt, [ t ] -> Z3.Arithmetic.Real.mk_real2int ctx t
      | T_irb.IntToBV size, [ t ] ->
          Z3.Arithmetic.Integer.mk_int2bv ctx (T_bv.bits_of size) t
      | T_irb.BVToInt size, [ t ] ->
          Z3.BitVector.mk_bv2int ctx t (T_bv.signed_of size)
      | FVar (var, _), ts when Map.Poly.mem fenv var ->
          Z3.FuncDecl.apply (Map.Poly.find_exn fenv var) ts
      | FVar (var, sorts), ts ->
          let sorts = List.map ~f:(of_sort ctx dtenv) sorts in
          let sargs, sret =
            (List.take sorts (List.length sorts - 1), List.last_exn sorts)
          in
          Z3.Expr.mk_app ctx
            (Z3.FuncDecl.mk_func_decl ctx (of_var ctx var) sargs sret)
            ts
      | T_tuple.TupleSel (sorts, i), [ t ] ->
          let sort = of_sort ctx dtenv @@ T_tuple.STuple sorts in
          Z3.FuncDecl.apply
            (List.nth_exn (Z3.Tuple.get_field_decls sort) i)
            [ t ]
      | T_tuple.TupleCons sorts, ts ->
          let sort = of_sort ctx dtenv @@ T_tuple.STuple sorts in
          Z3.FuncDecl.apply (Z3.Tuple.get_mk_decl sort) ts
      | T_dt.DTCons (name, _tys, dt), ts ->
          (*let dt = Datatype.update_args dt tys in*)
          Z3.FuncDecl.apply (z3_cons_of dtenv dt name) ts
      | T_dt.DTSel (name, dt, _), ts ->
          Z3.FuncDecl.apply (z3_sel_of dtenv dt name) ts
      | T_array.AStore (_si, _se), [ t1; t2; t3 ] ->
          Z3.Z3Array.mk_store ctx t1 t2 t3
      | T_array.ASelect (_si, _se), [ t1; t2 ] -> Z3.Z3Array.mk_select ctx t1 t2
      | T_array.AConst (si, _se), [ t1 ] ->
          Z3.Z3Array.mk_const_array ctx (of_sort ctx dtenv si) t1
      | T_string.StrConst str, [] -> Z3.Seq.mk_string ctx str
      | T_sequence.SeqEpsilon, [] -> Z3.FuncDecl.apply (z3_epsilon ctx) []
      | T_sequence.SeqSymbol str, [] ->
          Z3.FuncDecl.apply (z3_symbol_of ctx str) []
      | T_sequence.SeqConcat fin, [ t1; t2 ] ->
          Z3.FuncDecl.apply (z3_concat ctx fin) [ t1; t2 ]
      | T_regex.RegEmpty, [] ->
          Z3.Seq.mk_re_empty ctx @@ Z3.Seq.mk_re_sort ctx
          @@ Z3.Seq.mk_string_sort ctx
      | T_regex.RegFull, [] ->
          Z3.Seq.mk_re_full ctx @@ Z3.Seq.mk_re_sort ctx
          @@ Z3.Seq.mk_string_sort ctx
      | T_regex.RegEpsilon, [] ->
          Z3.Seq.mk_seq_to_re ctx (Z3.Seq.mk_string ctx "")
      | T_regex.RegStr, [ t1 ] -> Z3.Seq.mk_seq_to_re ctx t1
      | T_regex.RegComplement, [ t1 ] -> Z3.Seq.mk_re_complement ctx t1
      | T_regex.RegStar, [ t1 ] -> Z3.Seq.mk_re_star ctx t1
      | T_regex.RegPlus, [ t1 ] -> Z3.Seq.mk_re_plus ctx t1
      | T_regex.RegOpt, [ t1 ] -> Z3.Seq.mk_re_option ctx t1
      | T_regex.RegConcat, [ t1; t2 ] -> Z3.Seq.mk_re_concat ctx [ t1; t2 ]
      | T_regex.RegUnion, [ t1; t2 ] -> Z3.Seq.mk_re_union ctx [ t1; t2 ]
      | T_regex.RegInter, [ t1; t2 ] -> Z3.Seq.mk_re_intersect ctx [ t1; t2 ]
      | _ -> failwith @@ "[z3:of_term] not supported: " ^ Term.str_of t)

and (* Conversion from atoms to Z3 expressions *)
    of_atom ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) atom =
  if false then
    Debug.print @@ lazy (sprintf "[z3:of_atom] %s" @@ Atom.str_of atom);
  match atom with
  | True _ -> Z3.Boolean.mk_true ctx
  | False _ -> Z3.Boolean.mk_false ctx
  | App (Predicate.Var (pvar, _), args, _) ->
      if
        List.is_empty args
        && (not @@ List.Assoc.mem ~equal:Stdlib.( = ) penv pvar)
      then
        of_var_term ~id ctx env dtenv
        @@ Term.mk_var (Ident.pvar_to_tvar pvar) T_bool.SBool
      else
        let pred =
          match List.Assoc.find ~equal:Stdlib.( = ) penv pvar with
          | None ->
              failwith
              @@ sprintf "[z3:of_atom] %s not supported: "
              @@ Ident.name_of_pvar pvar
          | Some pred -> pred
        in
        Z3.Expr.mk_app ctx pred
        @@ List.map args ~f:(of_term ~id ctx env penv fenv dtenv)
  | App (Predicate.Fixpoint _, _, _) ->
      failwith @@ sprintf "[z3:of_atom] %s not supported" @@ Atom.str_of atom
  | App (Predicate.Psym sym, args, _) -> (
      (*if Stdlib.(sym = T_bool.Eq || sym = T_bool.Neq) &&
         (match args with [Term.FunApp (T_bool.Formula phi, [], _); _] -> not (Formula.is_true phi || Formula.is_false phi) | _ -> false) ||
         (match args with [_; Term.FunApp (T_bool.Formula phi, [], _)] -> not (Formula.is_true phi || Formula.is_false phi) | _ -> false) then
        if Stdlib.(sym = T_bool.Eq) then
          Boolean.mk_iff ctx
            (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn args)
            (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn @@ List.tl_exn args)
        else if Stdlib.(sym = T_bool.Neq) then
          Boolean.mk_xor ctx
            (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn args)
            (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn @@ List.tl_exn args)
        else assert false
        else*)
      match (sym, List.map ~f:(of_term ~id ctx env penv fenv dtenv) args) with
      | T_bool.Eq, [ t1; t2 ] -> Z3.Boolean.mk_eq ctx t1 t2
      | T_bool.Neq, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx @@ Z3.Boolean.mk_eq ctx t1 t2
      | (T_int.Leq | T_real.RLeq), [ t1; t2 ] -> Z3.Arithmetic.mk_le ctx t1 t2
      | T_bv.BVLeq size, [ t1; t2 ] ->
          (if T_bv.signed_of size then Z3.BitVector.mk_sle
           else Z3.BitVector.mk_ule)
            ctx t1 t2
      | (T_int.Geq | T_real.RGeq), [ t1; t2 ] -> Z3.Arithmetic.mk_ge ctx t1 t2
      | T_bv.BVGeq size, [ t1; t2 ] ->
          (if T_bv.signed_of size then Z3.BitVector.mk_sge
           else Z3.BitVector.mk_uge)
            ctx t1 t2
      | (T_int.Lt | T_real.RLt), [ t1; t2 ] -> Z3.Arithmetic.mk_lt ctx t1 t2
      | T_bv.BVLt size, [ t1; t2 ] ->
          (if T_bv.signed_of size then Z3.BitVector.mk_slt
           else Z3.BitVector.mk_ult)
            ctx t1 t2
      | (T_int.Gt | T_real.RGt), [ t1; t2 ] -> Z3.Arithmetic.mk_gt ctx t1 t2
      | T_bv.BVGt size, [ t1; t2 ] ->
          (if T_bv.signed_of size then Z3.BitVector.mk_sgt
           else Z3.BitVector.mk_ugt)
            ctx t1 t2
      | T_int.PDiv, [ t1; t2 ] ->
          Z3.Boolean.mk_eq ctx
            (Z3.Arithmetic.Integer.mk_mod ctx t2 t1)
            (Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
      | T_int.NotPDiv, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx
          @@ Z3.Boolean.mk_eq ctx
               (Z3.Arithmetic.Integer.mk_mod ctx t2 t1)
               (Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
      | T_irb.IsInt, [ t ] -> Z3.Arithmetic.Real.mk_is_integer ctx t
      | (T_num.NLeq _ | T_num.NGeq _ | T_num.NLt _ | T_num.NGt _), [ _t1; _t2 ]
        ->
          failwith
          @@ sprintf "[z3:of_atom] polymorphic inequalities not supported: %s"
          @@ Atom.str_of atom
      | T_tuple.IsTuple _sorts, _ts -> Z3.Boolean.mk_true ctx (*ToDo*)
      (*let _s = tuple_sort_of ctx dtenv sorts in
        let istuple = failwith "[z3:of_atom] is_tuple not supported" in
        Z3.FuncDecl.apply istuple ts*)
      | T_tuple.NotIsTuple _sorts, _ts -> Z3.Boolean.mk_false ctx (*ToDo*)
      (*let _s = tuple_sort_of ctx dtenv sorts in
        let istuple = failwith "[z3:of_atom] is_tuple not supported" in
        Boolean.mk_not ctx @@ Z3.FuncDecl.apply istuple ts*)
      | T_dt.IsCons (name, dt), ts ->
          Z3.FuncDecl.apply (z3_iscons_of dtenv dt name) ts
      | T_dt.NotIsCons (name, dt), ts ->
          Z3.Boolean.mk_not ctx
          @@ Z3.FuncDecl.apply (z3_iscons_of dtenv dt name) ts
      | T_sequence.IsPrefix fin, [ t1; t2 ] ->
          Z3.FuncDecl.apply (z3_is_prefix_of ctx fin) [ t1; t2 ]
      | T_sequence.NotIsPrefix fin, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx
          @@ Z3.FuncDecl.apply (z3_is_prefix_of ctx fin) [ t1; t2 ]
      | T_sequence.SeqInRegExp (fin, regexp), [ t1 ] ->
          Z3.FuncDecl.apply (z3_is_in_reg_exp ctx fin regexp) [ t1 ]
      | T_sequence.NotSeqInRegExp (fin, regexp), [ t1 ] ->
          Z3.Boolean.mk_not ctx
          @@ Z3.FuncDecl.apply (z3_is_in_reg_exp ctx fin regexp) [ t1 ]
      | T_regex.StrInRegExp, [ t1; t2 ] -> Z3.Seq.mk_seq_in_re ctx t1 t2
      | T_regex.NotStrInRegExp, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx @@ Z3.Seq.mk_seq_in_re ctx t1 t2
      | _ ->
          failwith
          @@ sprintf "[z3:of_atom] %s not supported"
          @@ Atom.str_of atom)

let z3_fenv_of ?(init = Map.Poly.empty) ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : FunEnv.t)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) =
  let z3_fenv =
    Map.Poly.fold fenv ~init
      ~f:(fun ~key:var ~data:(params, sret, _, _, _) acc ->
        if Map.Poly.mem acc var then acc
        else
          let func =
            Z3.FuncDecl.mk_rec_func_decl_s ctx (Ident.name_of_tvar var)
              (List.map params ~f:(snd >> of_sort ctx dtenv))
              (of_sort ctx dtenv sret)
          in
          Map.Poly.add_exn acc ~key:var ~data:func)
  in
  Map.Poly.iteri fenv ~f:(fun ~key:var ~data:(senv, _, def, _, _) ->
      if Map.Poly.mem init var then ()
      else
        Z3.FuncDecl.add_rec_def ctx
          (Map.Poly.find_exn z3_fenv var)
          (List.map senv
             ~f:(uncurry Term.mk_var >> of_term ~id ctx env penv z3_fenv dtenv))
          (of_term ~id ctx env penv z3_fenv dtenv def));
  z3_fenv

let of_formula_with_z3fenv ~id ctx (uni_senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) phi =
  let phi' =
    Formula.elim_let_equi false
    (*ToDo*) @@ Normalizer.normalize_let ~rename:true phi
  in
  Debug.print
  @@ lazy (sprintf "[z3:of_formula_with_z3fenv]\n  %s" (Formula.str_of phi'));
  of_formula_aux ~id ctx uni_senv penv fenv dtenv phi'
(*|> fun res ->
  Debug.print @@ lazy ("result: " ^ Z3.Expr.to_string res);
  res*)

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

let z3_solver_assert_and_track solver e1 e2 =
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.assert_and_track solver e1 e2

let check_sat_z3 ctx solver dtenv phis =
  z3_solver_add solver phis;
  (*Debug.print @@ lazy (Z3.Solver.to_string solver);*)
  match Z3.Solver.check solver [] with
  | SATISFIABLE -> (
      match z3_solver_get_model solver with
      | Some model ->
          (*print_endline @@ Z3.Model.to_string model;*)
          let model = model_of ctx dtenv model in
          (*debug_print_z3_model model;*)
          `Sat model
      | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE -> `Unsat
  | UNKNOWN -> (
      match Z3.Solver.get_reason_unknown solver with
      | "timeout" | "canceled" -> `Timeout
      | reason -> `Unknown reason)

let check_sat =
  let cfg = [ ("model", "true") ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  fun ?(timeout = None) ~id fenv phis ->
    let instance = get_instance id cfg instance_pool in
    let ctx, solver = (instance.ctx, instance.solver) in
    instance.dtenv <-
      z3_dtenv_of_formula ~init:instance.dtenv ctx @@ Formula.and_of phis;
    instance.fenv <-
      z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
    debug_print_z3_input phis;
    let phis = List.map phis ~f:(FunEnv.defined_formula_of fenv) in
    debug_print_z3_input phis;
    let phis' =
      List.map phis
        ~f:(of_formula_with_z3fenv ~id ctx [] [] instance.fenv instance.dtenv)
    in
    let params = Z3.Params.mk_params ctx in
    (match timeout with
    | None -> ()
    | Some timeout ->
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout);
    Z3.Solver.set_parameters solver params;
    let ret = check_sat_z3 ctx solver instance.dtenv phis' in
    back_instance
      ~reset:(fun instance -> z3_solver_reset instance.solver)
      instance_pool id instance;
    ret

let is_sat ~id fenv phi =
  match check_sat ~id fenv [ phi ] with `Sat _ -> true | _ -> false

let check_valid ~id fenv phi =
  match check_sat ~id fenv [ Formula.negate phi ] with
  | `Unsat -> `Valid
  | `Sat model -> `Invalid model
  | res -> res

let is_valid ~id fenv phi =
  Debug.print @@ lazy "[Z3interface.is_valid]";
  match check_valid ~id fenv phi with `Valid -> true | _ -> false

exception Unknown

let is_valid_exn ~id fenv phi =
  match check_valid ~id fenv phi with
  | `Valid -> true
  | `Invalid _ -> false
  | _ -> raise Unknown

(** [non_tracked] will be popped from solver when solving finished *)
let incr_check_sat_unsat_core ~id ?(z3str3 = false) ?(timeout = None)
    ?(non_tracked = Set.Poly.empty) solver ctx fenv dtenv pvar_clause_map =
  let f () =
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "model") true;
    Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "unsat_core") true;
    Z3.Params.add_symbol params
      (Z3.Symbol.mk_string ctx "smt.string_solver")
      (Z3.Symbol.mk_string ctx (if z3str3 then "z3str3" else "seq"));
    (match timeout with
    | None -> ()
    | Some timeout ->
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout);
    Z3.Solver.set_parameters solver params;
    Map.Poly.iteri pvar_clause_map ~f:(fun ~key:name ~data:phi ->
        if Formula.is_true phi then ()
        else (
          Debug.print
          @@ lazy
               (sprintf "assert and track: [%s] %s" name (Formula.str_of phi));
          let phi_expr = of_formula_with_z3fenv ~id ctx [] [] fenv dtenv phi in
          let label = Z3.Boolean.mk_const_s ctx name in
          z3_solver_assert_and_track solver phi_expr label));
    Z3.Solver.push solver;
    (*print_endline @@ Z3.Solver.to_string solver;*)
    let ret =
      Z3.Solver.add solver @@ Set.to_list
      @@ Set.Poly.map non_tracked
           ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv);
      match Z3.Solver.check solver [] with
      | Z3.Solver.SATISFIABLE -> (
          match z3_solver_get_model solver with
          | Some model -> `Sat (model_of ctx dtenv model)
          | None -> `Unknown "model production is not enabled?")
      | UNSATISFIABLE ->
          Debug.print @@ lazy "unsat reason:";
          let unsat_keys =
            List.map ~f:Z3.Expr.to_string @@ z3_solver_get_unsat_core solver
          in
          List.iter unsat_keys ~f:(fun unsat_key ->
              Debug.print @@ lazy unsat_key);
          `Unsat unsat_keys
      | UNKNOWN -> (
          match Z3.Solver.get_reason_unknown solver with
          | "timeout" | "canceled" -> `Timeout
          | reason -> (*print_endline reason;*) `Unknown reason)
    in
    Z3.Solver.pop solver 1;
    ret
  in
  match timeout with
  | None -> f ()
  | Some tm ->
      if tm = 0 then `Timeout (* times out immediately *)
      else
        Timer.enable_timeout (tm / 1000) Fn.id ignore f
          (fun _ res -> res)
          (fun _ -> function Timer.Timeout -> `Timeout | e -> raise e)

let check_sat_unsat_core ~id ?(z3str3 = false) ?(timeout = None) fenv
    pvar_clause_map =
  let ctx =
    let cfg = [ ("model", "true"); ("unsat_core", "true") ] in
    let cfg = if validate then cfg @ validate_cfg else cfg in
    let cfg =
      match timeout with
      | None -> cfg
      | Some timeout -> cfg @ [ ("timeout", string_of_int timeout) ]
    in
    Z3.mk_context cfg
  in
  let dtenv =
    z3_dtenv_of_formula ctx @@ Formula.and_of @@ List.map ~f:snd
    @@ Map.Poly.to_alist pvar_clause_map
  in
  let solver = Z3.Solver.mk_solver ctx None in
  let fenv = z3_fenv_of ~id ctx [] [] fenv dtenv in
  (match timeout with
  | None -> ()
  | Some timeout ->
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
      Z3.Solver.set_parameters solver params);
  incr_check_sat_unsat_core ~id ~z3str3 ~timeout solver ctx fenv dtenv
    pvar_clause_map

let max_smt_z3 ctx dtenv hard soft =
  let optimizer = Z3.Optimize.mk_opt ctx in
  Z3.Optimize.add optimizer hard;
  Map.Poly.iteri soft ~f:(fun ~key ~data ->
      List.iter data ~f:(fun (expr, weight) ->
          ignore
          @@ Z3.Optimize.add_soft optimizer expr (string_of_int weight)
               (Z3.Symbol.mk_string ctx key)));
  match Z3.Optimize.check optimizer with
  | SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Optimize.get_model optimizer >>= fun model ->
      let num_sat =
        Map.Poly.fold soft ~init:0 ~f:(fun ~key:_ ~data sum ->
            List.fold data ~init:sum ~f:(fun sum (expr, weight) ->
                sum
                +
                match Z3.Model.eval model expr true with
                | None -> 0
                | Some e -> if Z3.Boolean.is_true e then weight else 0))
      in
      Some (num_sat, model_of ctx dtenv model)
  | _ -> None

let max_smt ~id fenv hard soft =
  let cfg = [ ("MODEL", "true") (* ("well_sorted_check", "true"); *) ] in
  let ctx = Z3.mk_context cfg in
  let soft_phi =
    Map.Poly.to_alist soft |> List.map ~f:snd |> List.join |> List.map ~f:fst
    |> Formula.and_of
  in
  let dtenv = z3_dtenv_of_formula ctx @@ Formula.and_of (soft_phi :: hard) in
  let hard =
    List.map hard ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv)
  in
  let soft =
    Map.Poly.map soft
      ~f:
        (List.map ~f:(fun (phi, weight) ->
             (of_formula_with_z3fenv ~id ctx [] [] fenv dtenv phi, weight)))
  in
  max_smt_z3 ctx dtenv hard soft

(** ToDo: use MaxSMT instead *)
let max_smt_of ~id fenv num_ex phis =
  let cfg = [ ("unsat_core", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  instance.dtenv <-
    z3_dtenv_of_formula ~init:instance.dtenv ctx @@ Formula.and_of phis;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let solver = instance.solver in
  let name_map0 =
    List.map phis ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv)
    |> List.foldi ~init:Map.Poly.empty ~f:(fun i map phi ->
           let name = "#S_" ^ string_of_int i in
           let label = Z3.Boolean.mk_const_s ctx name in
           Map.Poly.update map label ~f:(function None -> phi | Some x -> x))
  in
  let rec inner num_ex models ignored name_map =
    if num_ex <= 0 then models
    else (
      Map.Poly.iteri name_map ~f:(fun ~key ~data ->
          z3_solver_assert_and_track solver data key);
      z3_solver_reset solver;
      match Z3.Solver.check solver [] with
      | Z3.Solver.SATISFIABLE -> (
          match z3_solver_get_model solver with
          | None -> assert false
          | Some model ->
              let models' = Set.add models (model_of ctx dtenv model) in
              let name_map' =
                Map.Poly.filter_keys ~f:(Set.mem ignored) name_map0
              in
              inner (num_ex - 1) models' Set.Poly.empty name_map')
      | UNSATISFIABLE ->
          let ucore = List.hd_exn @@ z3_solver_get_unsat_core solver in
          inner num_ex models (Set.add ignored ucore)
            (Map.Poly.remove name_map ucore)
      | UNKNOWN -> assert false)
  in
  inner num_ex Set.Poly.empty Set.Poly.empty name_map0 |> fun ret ->
  back_instance
    ~reset:(fun ins -> z3_solver_reset ins.solver)
    instance_pool id instance;
  ret

let check_opt_maximize_z3 ctx dtenv phis obj =
  let optimizer = Z3.Optimize.mk_opt ctx in
  Z3.Optimize.add optimizer phis;
  let handle = Z3.Optimize.maximize optimizer obj in
  match Z3.Optimize.check optimizer with
  | SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Optimize.get_model optimizer >>= fun model ->
      let lower = Z3.Optimize.get_lower handle |> term_of ctx [] [] dtenv in
      let upper = Z3.Optimize.get_upper handle |> term_of ctx [] [] dtenv in
      Some (lower, upper, model_of ctx dtenv model)
  | _ -> None

let check_opt_maximize ~id fenv phis obj =
  let cfg = [ ("model", "true") ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  let ctx = Z3.mk_context cfg in
  let dtenv = z3_dtenv_of_formula ctx @@ Formula.and_of phis in
  let z3fenv = z3_fenv_of ~id ctx [] [] fenv dtenv in
  debug_print_z3_input phis;
  let phis =
    List.map phis ~f:(of_formula_with_z3fenv ~id ctx [] [] z3fenv dtenv)
  in
  let obj =
    of_term ~id ctx [] [] (z3_fenv_of ~id ctx [] [] fenv dtenv) dtenv obj
  in
  check_opt_maximize_z3 ctx dtenv phis obj

let penv_of phi ctx dtenv =
  Formula.pred_sort_env_of phi
  |> Set.to_list
  |> List.map ~f:(pred_decl_of ctx dtenv)

(** assume that [phi] is alpha-renamed *)
let z3_simplify ~id fenv phi =
  let cfg = [ ("model", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let penv = penv_of phi ctx dtenv in
  let tenv =
    let lenv = Map.Poly.to_alist @@ Formula.let_sort_env_of phi in
    lenv @ Set.to_list @@ Formula.term_sort_env_of phi
  in

  let symplify_params = Z3.Params.mk_params ctx in
  Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "elim_ite") true;
  Z3.Params.add_bool symplify_params
    (Z3.Symbol.mk_string ctx "push_ite_arith")
    true;

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
        (* |> (fun phi -> print_endline @@ "before: " ^ Formula.str_of phi ^ "\n"; phi) *)
        |> of_formula_with_z3fenv ~id ctx tenv penv fenv dtenv
        |> Fn.flip Z3.Expr.simplify @@ Some symplify_params
        |> formula_of ctx (List.rev tenv) penv dtenv
        |> Evaluator.simplify
    (* |> (fun phi -> print_endline @@ "after: " ^ Formula.str_of phi ^ "\n"; phi) *)
  in
  let ret = inner phi in
  back_instance ~reset:ignore instance_pool id instance;
  ret

let qelim ~id ~fenv phi =
  Debug.print @@ lazy "[Z3interface.qelim]";
  if
    Set.for_all (Formula.funsyms_of phi) ~f:(T_bv.is_bv_fsym >> not)
    && Set.for_all (Formula.predsyms_of phi) ~f:(T_bv.is_bv_psym >> not)
    (*&& Formula.is_quantifier_free phi*)
  then (
    Debug.print @@ lazy (sprintf "[z3:qelim] %s" (Formula.str_of phi));
    let cfg = [ ("model", "true") ] in
    let instance = get_instance id cfg instance_pool in
    let ctx = instance.ctx in
    let goal = instance.goal in
    instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
    instance.fenv <-
      z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
    let symplify_params = Z3.Params.mk_params ctx in
    let penv = penv_of phi ctx instance.dtenv in
    Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "elim_ite") true;
    let qe_params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool qe_params
      (Z3.Symbol.mk_string ctx "eliminate_variables_as_block")
      true;
    let expr =
      of_formula_with_z3fenv ~id ctx [] penv instance.fenv instance.dtenv phi
    in
    Debug.print @@ lazy ("[qelim] input: " ^ Z3.Expr.to_string expr);
    z3_goal_add goal [ expr ];
    let g =
      Z3.Goal.as_expr
      @@ Z3.Tactic.ApplyResult.get_subgoal
           (Z3.Tactic.apply
              (Z3.Tactic.mk_tactic ctx "qe")
              goal (Some qe_params))
           0
    in
    let expr = Z3.Expr.simplify g (Some symplify_params) in
    Debug.print @@ lazy ("[qelim] output: " ^ Z3.Expr.to_string expr);
    let phi =
      Evaluator.simplify @@ Formula.nnf_of
      @@ formula_of ctx [] penv instance.dtenv expr
    in
    back_instance
      ~reset:(fun ins -> Z3.Goal.reset ins.goal)
      instance_pool id instance;
    (* print_endline @@ "qelim ret: " ^ Formula.str_of phi; *)
    phi)
  else phi

let smtlib2_str_of_formula ~id ctx fenv dtenv phi =
  Z3.Expr.to_string
  @@ of_formula_with_z3fenv ~id ctx
       (Set.to_list @@ Formula.term_sort_env_of phi)
       (penv_of phi ctx dtenv) fenv dtenv phi

let expr_of_default_true ~id ctx fenv dtenv phi =
  try of_formula_with_z3fenv ~id ctx [] [] fenv dtenv @@ Evaluator.simplify phi
  with _ ->
    of_formula_with_z3fenv ~id ctx [] [] fenv dtenv @@ Formula.mk_true ()

let str_of_asserts_of_solver solver =
  "Asserts of solver:\n\t"
  ^ String.concat_map_list ~sep:"\n\t" ~f:Z3.Expr.to_string
  @@ Z3.Solver.get_assertions solver

let inc_check_valid solver exprs =
  (*Debug.print @@ lazy (sprintf "checking validity of %s\n%s\n" (String.concat_map_list ~sep:" /\ " ~f:Expr.to_string exprs)) (str_of_asserts_of_solver solver);*)
  match Z3.Solver.check solver exprs with
  | SATISFIABLE ->
      (*Debug.print @@ lazy (sprintf "check valid -> (sat)invalid");*)
      false
  | UNSATISFIABLE ->
      (*Debug.print @@ lazy (sprintf "checksat valid -> (unsat)valid");*)
      true
  | _ -> failwith "inc_check_valid"

let star and_flag = function
  | Formula.Atom (a, _) when Atom.is_pvar_app a -> None
  | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _)
    when Atom.is_pvar_app a ->
      None
  | phi ->
      Some (Evaluator.simplify @@ if and_flag then phi else Formula.negate phi)

let rec simplify_term ~id solver ctx fenv dtenv = function
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      let phi, has_changed = simplify_formula ~id solver ctx fenv dtenv phi in
      (T_bool.of_formula ~info phi, has_changed)
  | Term.FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
      let t1, has_changed1 = simplify_term ~id solver ctx fenv dtenv t1 in
      let t2, has_changed2 =
        (*ToDo: add t1 to the context*)
        simplify_term ~id solver ctx fenv dtenv t2
      in
      let t3, has_changed3 =
        (*ToDo: add not t1 to the context*)
        simplify_term ~id solver ctx fenv dtenv t3
      in
      ( T_bool.mk_if_then_else ~info t1 t2 t3,
        has_changed1 || has_changed2 || has_changed3 )
  | t (*ToDo*) -> (t, false)

and simplify_atom ~id solver ctx fenv (dtenv : dtenv) atom =
  if Atom.is_pvar_app atom then
    let pvar, sorts, args, info = Atom.let_pvar_app atom in
    let args', _has_changed_list =
      List.unzip @@ List.map ~f:(simplify_term ~id solver ctx fenv dtenv) args
    in
    ( Atom.mk_pvar_app pvar sorts args' ~info,
      false (*List.exists ~f:ident has_changed_list*) )
  else
    let phi = Formula.mk_atom atom in
    (* Debug.print @@ lazy (sprintf "simplify atom: %s" (Formula.str_of phi)); *)
    if
      inc_check_valid solver
        [ expr_of_default_true ~id ctx fenv dtenv @@ Formula.negate phi ]
    then (Atom.mk_true (), true)
    else if
      inc_check_valid solver [ expr_of_default_true ~id ctx fenv dtenv @@ phi ]
    then (Atom.mk_false (), true)
    else (atom, false)

and check_sub_formulas ~id level solver ctx fenv (dtenv : dtenv) and_flag phi =
  let cs =
    List.map ~f:snd
    @@ List.sort ~compare:(fun (n1, _) (n2, _) -> n1 - n2)
    @@ List.map ~f:(fun x -> (Formula.ast_size x, x))
    @@ Set.to_list
    @@ if and_flag then Formula.conjuncts_of phi else Formula.disjuncts_of phi
  in
  (*print_endline @@ String.init level ~f:(fun _ -> ' ') ^ string_of_int @@ List.length cs;*)
  (* Debug.print @@ lazy (sprintf "Cs: %s" (String.concat_map_list ~sep:"\n\t" cs ~f:Formula.str_of)); *)
  (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
  try
    Z3.Solver.push solver;
    let cs', _, has_changed =
      List.fold_left cs
        ~init:([], List.tl_exn cs, false)
        ~f:(fun (cs', cs, has_changed) c ->
          (* Debug.print @@ lazy (sprintf "c: %s" (Formula.str_of c)); *)
          Z3.Solver.push solver;
          z3_solver_add solver
          @@ List.map ~f:(expr_of_default_true ~id ctx fenv dtenv)
          @@ List.filter_map cs ~f:(star and_flag);
          (* Debug.print @@ lazy (str_of_asserts_of_solver solver); *)
          let c', has_changed' =
            simplify_formula ~id ~level:(level + 1) solver ctx fenv dtenv c
          in
          Z3.Solver.pop solver 1;
          (* Debug.print @@ lazy (sprintf "c': %s" (Formula.str_of c')); *)
          if
            (and_flag && Formula.is_false c')
            || ((not and_flag) && Formula.is_true c')
          then raise @@ Stdlib.Not_found
          else (
            (match star and_flag c' with
            | Some phi ->
                z3_solver_add solver
                @@ [ expr_of_default_true ~id ctx fenv dtenv phi ]
            | None -> ());
            ( c' :: cs',
              (match cs with _ :: tl -> tl | _ -> []),
              has_changed || has_changed' )))
    in
    Z3.Solver.pop solver 1;
    let cs' = List.rev cs' in
    (*if has_changed then
      Debug.print @@ lazy
        (sprintf "compare Cs to Cs':\nCs: %s\nCs': %s"
           (String.concat_map_list ~sep:"\n\t" cs ~f:Formula.str_of)
           (String.concat_map_list ~sep:"\n\t" cs' ~f:Formula.str_of));*)
    let ret =
      Evaluator.simplify
      @@ if and_flag then Formula.and_of cs' else Formula.or_of cs'
    in
    if has_changed then
      (* Debug.print @@ lazy ("has changed."); *)
      ( fst @@ check_sub_formulas ~id level solver ctx fenv dtenv and_flag ret,
        true )
    else (ret, false)
  with Stdlib.Not_found ->
    Z3.Solver.pop solver 1;
    ((if and_flag then Formula.mk_false () else Formula.mk_true ()), true)

and simplify_formula ~id ?(level = 0) solver ctx fenv (dtenv : dtenv) phi =
  (*Debug.print @@ lazy (sprintf "[z3:simplify_formula] input: %s" (Formula.str_of phi));
    Debug.print @@ lazy (str_of_asserts_of_solver solver);*)
  let res =
    match phi with
    | Formula.Atom (atom, _) when not (Atom.is_true atom || Atom.is_false atom)
      ->
        let atom, has_changed = simplify_atom ~id solver ctx fenv dtenv atom in
        (Formula.mk_atom atom, has_changed)
    | Formula.UnaryOp (Not, Atom (atom, _), _)
      when not (Atom.is_true atom || Atom.is_false atom) ->
        let atom, has_changed = simplify_atom ~id solver ctx fenv dtenv atom in
        (Formula.negate (Formula.mk_atom atom), has_changed)
    | Formula.BinaryOp (And, _, _, _) ->
        check_sub_formulas ~id level solver ctx fenv dtenv true phi
    | Formula.BinaryOp (Or, _, _, _) ->
        check_sub_formulas ~id level solver ctx fenv dtenv false phi
    | Formula.LetFormula (var, sort, def, body, info) ->
        let def, _ = simplify_term ~id solver ctx fenv dtenv def in
        let body, has_changed =
          simplify_formula ~id ~level solver ctx fenv dtenv body
        in
        (Formula.LetFormula (var, sort, def, body, info), has_changed)
    | _ -> (phi, false)
  in
  (*Debug.print @@ lazy (sprintf "[z3:simplify_formula] output: %s" (Formula.str_of @@ fst res));*)
  res

and simplify ?(timeout = None) ~id fenv phi =
  Debug.print @@ lazy "===========simplify start=============";
  Debug.print @@ lazy (sprintf "input: %s" @@ Formula.str_of phi);
  let cfg = [ ("model", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx, solver = (instance.ctx, instance.solver) in
  instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  (* Debug.print @@ lazy
     (sprintf "the smtlib2 formua:\n\t%s" @@ smtlib2_str_of_formula ctx dtenv phi); *)
  (* let solver = Z3.Solver.mk_solver ctx None in *)
  let params = Z3.Params.mk_params ctx in
  (match timeout with
  | None -> ()
  | Some timeout ->
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout);
  Z3.Solver.set_parameters solver params;
  let phi = Normalizer.normalize_let phi in
  let phi = z3_simplify ~id fenv @@ Formula.nnf_of phi in
  Debug.print @@ lazy "*** start ***";
  let phi =
    fst @@ simplify_formula ~id solver ctx instance.fenv instance.dtenv phi
  in
  Debug.print @@ lazy "*** end ***";
  let phi = z3_simplify ~id fenv phi in
  Debug.print
  @@ lazy
       (sprintf "output: %s\n===========simplify end============="
          (Formula.str_of phi));
  back_instance
    ~reset:(fun instance -> z3_solver_reset instance.solver)
    instance_pool id instance;
  phi

(** For external calls *)
let of_formula ~id ctx env penv fenv dtenv phi =
  of_formula_with_z3fenv ~id ctx env penv
    (z3_fenv_of ~id ctx env penv fenv dtenv)
    dtenv phi
