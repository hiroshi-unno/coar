open Ast
open Ast.LogicOld

exception SyntaxError of string
exception SemanticError of string

module Define = struct
  type t = DEF of (string * int)
  let mk_def key value = DEF (key, value)
  let let_def = function DEF (key, value) -> key, value
  let rec subst_of_defines = function
    | [] -> Core.Map.Poly.empty
    | DEF (key, value) :: tail ->
      let tvar = Ident.Tvar key in
      let term = T_int.mk_int (Z.of_int value) in
      Core.Map.Poly.add_exn (subst_of_defines tail) ~key:tvar ~data:term
end

module rec Ctl : sig
  type t =
      AF of t
    | EF of t
    | AG of t
    | EG of t
    | OR of t * t
    | AND of t * t
    | IMP of t * t
    | AP of Formula.t

  type unwrap_result =
    | PHI of t
    | PHI2 of t * t
    | FORMULA of Formula.t

  val is_af: t -> bool
  val is_ef: t -> bool
  val is_ag: t -> bool
  val is_eg: t -> bool
  val is_and: t -> bool
  val is_or: t -> bool
  val is_imp: t -> bool
  val is_ap: t -> bool

  val is_unop: t -> bool
  val is_binop: t -> bool

  val is_a: t -> bool
  val is_e: t -> bool
  val is_f: t -> bool
  val is_g: t -> bool

  val mk_af: t -> t
  val mk_ef: t -> t
  val mk_ag: t -> t
  val mk_eg: t -> t
  val mk_and: t -> t -> t
  val mk_or: t -> t -> t
  val mk_imp: t -> t -> t
  val mk_ap: Formula.t -> t

  val let_af: t -> t
  val let_ef: t -> t
  val let_ag: t -> t
  val let_eg: t -> t
  val let_ap: t -> Formula.t

  val string_of: t -> string
  val get_fv: t -> Variables.t
  val unwrap: t -> unwrap_result
  val let_unop: t -> t
  val let_binop: t -> Formula.binop * t * t

  val get_inner_phis: t -> t list
end = struct
  type t =
      AF of t
    | EF of t
    | AG of t
    | EG of t
    | OR of t * t
    | AND of t * t
    | IMP of t * t
    | AP of Formula.t

  type unwrap_result =
    | PHI of t
    | PHI2 of t * t
    | FORMULA of Formula.t

  let is_af = function AF _ -> true | _ -> false
  let is_ef = function EF _ -> true | _ -> false
  let is_ag = function AG _ -> true | _ -> false
  let is_eg = function EG _ -> true | _ -> false
  let is_and = function AND _ -> true | _ -> false
  let is_or = function OR _ -> true | _ -> false
  let is_imp = function IMP _ -> true | _ -> false
  let is_ap = function AP _ -> true | _ -> false

  let is_unop = function AF _ | EF _ | AG _ | EG _ -> true | _ -> false
  let is_binop = function OR _ | AND _ | IMP _ -> true | _ -> false

  let is_a = function AF _ | AG _ -> true | _ -> false
  let is_e = function EF _ | EG _ -> true | _ -> false
  let is_f = function AF _ | EF _ -> true | _ -> false
  let is_g = function AG _ | EG _ -> true | _ -> false

  let mk_af phi = AF phi
  let mk_ef phi = EF phi
  let mk_ag phi = AG phi
  let mk_eg phi = EG phi
  let mk_and phi1 phi2 = AND (phi1, phi2)
  let mk_or phi1 phi2 = OR (phi1, phi2)
  let mk_imp phi1 phi2 = IMP (phi1, phi2)
  let mk_ap fml = AP fml

  let let_af = function AF phi -> phi | _ -> assert false
  let let_ef = function EF phi -> phi | _ -> assert false
  let let_ag = function AG phi -> phi | _ -> assert false
  let let_eg = function EG phi -> phi | _ -> assert false
  let let_ap = function AP fml -> fml | _ -> assert false

  let rec string_of = function
    | AF phi -> Printf.sprintf "AF(%s)" (string_of phi)
    | EF phi -> Printf.sprintf "EF(%s)" (string_of phi)
    | AG phi -> Printf.sprintf "AG(%s)" (string_of phi)
    | EG phi -> Printf.sprintf "EG(%s)" (string_of phi)
    | OR (phi1, phi2) -> Printf.sprintf "OR(%s, %s)" (string_of phi1) (string_of phi2)
    | AND (phi1, phi2) -> Printf.sprintf "AND(%s, %s)" (string_of phi1) (string_of phi2)
    | IMP (phi1, phi2) -> Printf.sprintf "IMP(%s, %s)" (string_of phi1) (string_of phi2)
    | AP fml -> Printf.sprintf "AP(%s)" (Formula.str_of fml)

  let rec get_fv = function
    | AF phi | EF phi | AG phi | EG phi -> get_fv phi
    | OR (phi1, phi2) | AND (phi1, phi2) | IMP (phi1, phi2) ->
      Variables.union (get_fv phi1) (get_fv phi2)
    | AP fml ->
      Formula.tvs_of fml
      |> Core.Set.Poly.to_list
      |> List.map Ast.Ident.name_of_tvar
      |> Variables.of_list

  let unwrap = function
    | AF phi | EF phi | AG phi | EG phi -> PHI phi
    | OR (phi1, phi2) | AND (phi1, phi2) | IMP (phi1, phi2) -> PHI2 (phi1, phi2)
    | AP fml -> FORMULA fml

  let let_unop phi =
    match unwrap phi with
    | PHI phi -> phi
    | _ -> assert false

  let let_binop phi =
    match phi with
    | OR (phi1, phi2) -> Formula.Or, phi1, phi2
    | AND (phi1, phi2) -> Formula.And, phi1, phi2
    | IMP (phi1, phi2) -> Formula.Imply, phi1, phi2
    | _ -> assert false

  let get_inner_phis phi =
    match unwrap phi with
    | PHI phi -> [phi]
    | PHI2 (phi1, phi2) -> [phi1; phi2]
    | FORMULA _ -> []
end

module rec Declare : sig
  type t =
      INT of string

  val is_int: t -> bool

  val mk_int: string -> t

  val let_int: t -> string

  val string_of: t -> string
end = struct
  type t =
      INT of string

  let is_int = function INT _ -> true

  let mk_int varname = INT varname

  let let_int = function INT varname -> varname

  let string_of = function
    | INT varname -> Printf.sprintf "int %s;" varname
end

module rec Statement : sig
  type t =
      IF of Formula.t * t * t
    | LOOP of t
    | ASSIGN of string * Term.t
    | NONDET_ASSIGN of string
    | COMPOUND of t * t
    | NONDET of t * t
    | ASSUME of Formula.t
    | CALL_VOIDFUN of string * Term.t list
    | CALL_ASSIGN of string * string * Term.t list
    | BREAK
    | EXIT
    | NOP

  val is_if: t -> bool
  val is_loop: t -> bool
  val is_assign: t -> bool
  val is_nondet_assign: t -> bool
  val is_compound: t -> bool
  val is_nondet: t -> bool
  val is_assume: t -> bool
  val is_call_voidfun: t -> bool
  val is_call_assign: t -> bool
  val is_break: t -> bool
  val is_exit: t -> bool
  val is_nop: t -> bool

  val mk_if: Formula.t -> t -> t -> t
  val mk_loop: t -> t
  val mk_assign: string -> Term.t -> t
  val mk_nondet_assign: string -> t
  val mk_compound: t -> t -> t
  val mk_nondet: t -> t -> t
  val mk_assume: Formula.t -> t
  val mk_call_voidfun: string -> Term.t list -> t
  val mk_call_assign: string -> string -> Term.t list -> t
  val mk_break: unit -> t
  val mk_exit: unit -> t
  val mk_nop: unit -> t

  val let_if: t -> Formula.t * t * t
  val let_loop: t -> t
  val let_assign: t -> string * Term.t
  val let_nondet_assign: t -> string
  val let_compound: t -> t * t
  val let_nondet: t -> t * t
  val let_assume: t -> Formula.t
  val let_call_voidfun: t -> string * Term.t list
  val let_call_assign: t -> string * string * Term.t list

  val string_of: ?indent:int -> t -> string
  val subst: (Ident.tvar, Term.t) Core.Map.Poly.t -> t -> t
  val get_inner_statements: t -> t list
  val get_read_vars: t -> Variables.t
end = struct
  type t =
      IF of Formula.t * t * t
    | LOOP of t
    | ASSIGN of string * Term.t
    | NONDET_ASSIGN of string
    | COMPOUND of t * t
    | NONDET of t * t
    | ASSUME of Formula.t
    | CALL_VOIDFUN of string * Term.t list
    | CALL_ASSIGN of string * string * Term.t list
    | BREAK
    | EXIT
    | NOP

  let is_if = function IF _ -> true | _ -> false
  let is_loop = function LOOP _ -> true | _ -> false
  let is_assign = function ASSIGN _ -> true | _ -> false
  let is_nondet_assign = function NONDET_ASSIGN _ -> true | _ -> false
  let is_compound = function COMPOUND _ -> true | _ -> false
  let is_nondet = function NONDET _ -> true | _ -> false
  let is_assume = function ASSUME _ -> true | _ -> false
  let is_call_voidfun = function CALL_VOIDFUN _ -> true | _ -> false
  let is_call_assign = function CALL_ASSIGN _ -> true | _ -> false
  let is_break = function BREAK -> true | _ -> false
  let is_exit = function EXIT -> true | _ -> false
  let is_nop = function NOP -> true | _ -> false

  let mk_if cond_fml t_stmt f_stmt = IF (cond_fml, t_stmt, f_stmt)
  let mk_loop stmt = LOOP stmt
  let mk_assign varname term = ASSIGN (varname, term)
  let mk_nondet_assign varname = NONDET_ASSIGN varname
  let mk_compound stmt1 stmt2 = COMPOUND (stmt1, stmt2)
  let mk_nondet stmt1 stmt2 = NONDET (stmt1, stmt2)
  let mk_assume fml = ASSUME fml
  let mk_call_voidfun funname args = CALL_VOIDFUN (funname, args)
  let mk_call_assign varname funname args = CALL_ASSIGN (varname, funname, args)
  let mk_break () = BREAK
  let mk_exit () = EXIT
  let mk_nop () = NOP

  let let_if = function IF (cond_fml, t_stmt, f_stmt) -> cond_fml, t_stmt, f_stmt | _ -> assert false
  let let_loop = function LOOP stmt -> stmt | _ -> assert false
  let let_assign = function ASSIGN (varname, term) -> varname, term | _ -> assert false
  let let_nondet_assign = function NONDET_ASSIGN varname -> varname | _ -> assert false
  let let_compound = function COMPOUND (stmt1, stmt2) -> stmt1, stmt2 | _ -> assert false
  let let_nondet = function NONDET (stmt1, stmt2) -> stmt1, stmt2 | _ -> assert false
  let let_assume = function ASSUME fml -> fml | _ -> assert false
  let let_call_voidfun = function CALL_VOIDFUN (funname, args) -> funname, args | _ -> assert false
  let let_call_assign = function CALL_ASSIGN (varname, funname, args) -> varname, funname, args | _ -> assert false

  let make_indent indent = String.make indent ' '

  let string_of_args args =
    args
    |> List.map Term.str_of
    |> String.concat ", "

  let rec string_of ?(indent=0) = function
    | IF (cond_fml, t_stmt, f_stmt) ->
      if is_nop f_stmt then
        Printf.sprintf "%sif (%s) {\n%s\n%s}"
          (make_indent indent)
          (Formula.str_of cond_fml)
          (string_of ~indent:(indent+2) t_stmt)
          (make_indent indent)
      else
        Printf.sprintf "%sif (%s) {\n%s\n%s}\n%selse {\n%s\n%s}"
          (make_indent indent)
          (Formula.str_of cond_fml)
          (string_of ~indent:(indent+2) t_stmt)
          (make_indent indent)
          (make_indent indent)
          (string_of ~indent:(indent+2) f_stmt)
          (make_indent indent)
    | LOOP stmt ->
      Printf.sprintf "%swhile (1) {\n%s\n%s}"
        (make_indent indent)
        (string_of ~indent:(indent+2) stmt)
        (make_indent indent)
    | ASSIGN (varname, term) ->
      Printf.sprintf "%s%s = %s;"
        (make_indent indent)
        varname
        (Term.str_of term)
    | NONDET_ASSIGN varname ->
      Printf.sprintf "%s%s = nondet();"
        (make_indent indent)
        varname
    | COMPOUND (stmt1, stmt2) ->
      Printf.sprintf "%s\n%s"
        (string_of ~indent stmt1)
        (string_of ~indent stmt2)
    | NONDET (stmt1, stmt2) ->
      Printf.sprintf "%snondet {\n%s\n%s}\n%selse {\n%s\n%s}"
        (make_indent indent)
        (string_of ~indent:(indent+2) stmt1)
        (make_indent indent)
        (make_indent indent)
        (string_of ~indent:(indent+2) stmt2)
        (make_indent indent)
    | ASSUME fml ->
      Printf.sprintf "%sassume(%s);"
        (make_indent indent)
        (Formula.str_of fml)
    | CALL_VOIDFUN (funname, args) ->
      Printf.sprintf "%s%s(%s);"
        (make_indent indent)
        funname
        (string_of_args args)
    | CALL_ASSIGN (varname, funname, args) ->
      Printf.sprintf "%s%s = %s(%s);"
        (make_indent indent)
        varname
        funname
        (string_of_args args)
    | BREAK -> Printf.sprintf "%sbreak;" (make_indent indent)
    | EXIT -> Printf.sprintf "%sexit 0;" (make_indent indent)
    | NOP -> Printf.sprintf "%snop;" (make_indent indent)

  let subst_args sub args =
    args
    |> List.map (Term.subst sub)

  let rec subst sub stmt =
    match stmt with
    | IF (cond_fml, t_stmt, f_stmt) ->
      let t_stmt = subst sub t_stmt in
      let f_stmt = subst sub f_stmt in
      mk_if (Formula.subst sub cond_fml) t_stmt f_stmt
    | LOOP stmt' ->
      let stmt' = subst sub stmt' in
      mk_loop stmt'
    | ASSIGN (varname, term) ->
      mk_assign varname (Term.subst sub term)
    | NONDET (stmt1, stmt2) ->
      let stmt1 = subst sub stmt1 in
      let stmt2 = subst sub stmt2 in
      mk_nondet stmt1 stmt2
    | COMPOUND (stmt1, stmt2) ->
      let stmt1 = subst sub stmt1 in
      let stmt2 = subst sub stmt2 in
      mk_compound stmt1 stmt2
    | ASSUME fml ->
      mk_assume (Formula.subst sub fml)
    | CALL_VOIDFUN (funname, args) ->
      mk_call_voidfun funname (subst_args sub args)
    | CALL_ASSIGN (varname, funname, args) ->
      mk_call_assign varname funname (subst_args sub args)
    | NONDET_ASSIGN _
    | BREAK
    | EXIT
    | NOP ->
      stmt

  let rec get_read_vars = function
    | IF (cond_fml, t_stmt, f_stmt) ->
      Formula.tvs_of cond_fml
      |> Variables.of_tvarset
      |> Variables.union (get_read_vars t_stmt)
      |> Variables.union (get_read_vars f_stmt)
    | LOOP stmt' ->
      get_read_vars stmt'
    | ASSIGN (_, term) ->
      Term.tvs_of term
      |> Variables.of_tvarset
    | NONDET (stmt1, stmt2)
    | COMPOUND (stmt1, stmt2) ->
      get_read_vars stmt1
      |> Variables.union (get_read_vars stmt2)
    | ASSUME fml ->
      Formula.tvs_of fml
      |> Variables.of_tvarset
    | CALL_VOIDFUN (_, args)
    | CALL_ASSIGN (_, _, args) ->
      List.fold_left
        (fun vars arg ->
           Term.tvs_of arg
           |> Variables.of_tvarset
           |> Variables.union vars
        )
        Variables.empty
        args
    | NONDET_ASSIGN _
    | BREAK
    | EXIT
    | NOP ->
      Variables.empty

  let get_inner_statements = function
    | IF (_, stmt1, stmt2)
    | NONDET (stmt1, stmt2)
    | COMPOUND (stmt1, stmt2) ->
      [stmt1; stmt2]
    | LOOP stmt ->
      [stmt]
    | ASSIGN _
    | ASSUME _
    | CALL_VOIDFUN _
    | CALL_ASSIGN _
    | NONDET_ASSIGN _
    | BREAK
    | EXIT
    | NOP ->
      []
end

module rec Init : sig
  type t =
      ASSIGN of string * Term.t
    | ASSUME of Formula.t

  val is_assign: t -> bool
  val is_assume: t -> bool

  val mk_assign: string -> Term.t -> t
  val mk_assume: Formula.t -> t

  val let_assign: t -> string * Term.t
  val let_assume: t -> Formula.t

  val string_of: t -> string
  val update_state: State.t -> t -> State.t
  val update_formula: Formula.t -> t -> Formula.t
  val subst: (Ident.tvar, Term.t) Core.Map.Poly.t -> t -> t

  val update_varname: string -> t -> t
end = struct
  type t =
      ASSIGN of string * Term.t
    | ASSUME of Formula.t

  let is_assign = function ASSIGN _ -> true | _ -> false
  let is_assume = function ASSUME _ -> true | _ -> false

  let mk_assign varname term = ASSIGN (varname, term)
  let mk_assume fml = ASSUME fml

  let let_assign = function ASSIGN (varname, term) -> varname, term | _ -> assert false
  let let_assume = function ASSUME fml -> fml | _ -> assert false

  let update_varname varname = function
    | ASSIGN (_, term) -> ASSIGN (varname, term)
    | _ -> assert false

  let string_of = function
    | ASSIGN (varname, term) ->
      Printf.sprintf "%s = %s;"
        varname
        (Term.str_of term)
    | ASSUME fml ->
      Printf.sprintf "assume(%s);"
        (Formula.str_of fml)

  let update_state state = function
    | ASSIGN (varname, term) ->
      State.update varname term state
    | ASSUME _ -> state

  let update_formula fml = function
    | ASSIGN _ -> fml
    | ASSUME fml' ->
      Formula.mk_imply fml' fml

  let subst sub = function
    | ASSIGN (varname, term) ->
      mk_assign varname (Term.subst sub term)
    | ASSUME fml ->
      mk_assume (Formula.subst sub fml)
end

and State : sig
  type t = STATE of (string * Term.t ref) list

  val of_variables: Variables.t -> t
  val update: string -> Term.t -> t -> t
  val bounds_of: t -> SortEnv.t
  val appformula_of: Ident.pvar -> t -> Formula.t
  val get: string -> t -> Term.t
  val mem: string -> t -> bool
  val of_inits: Init.t list -> t
end = struct
  type t = STATE of (string * Term.t ref) list

  let of_variables variables =
    let state =
      Variables.to_list variables
      |> List.map (fun varname -> varname, ref (Term.mk_var (Ident.Tvar varname) T_int.SInt))
    in
    STATE state

  (* let lookup varname = function STATE state ->
     (match List.assoc_opt varname state with
     | None -> raise (Error (Printf.sprintf "variable %s is not defined" varname))
     | Some term -> term) *)

  let update varname term = function STATE state ->
  try
    List.assoc varname state := term;
    STATE state
  with
    Not_found ->
    STATE state

  let bounds_of = function STATE state ->
    SortEnv.of_list @@ List.map (fun (varname, _) -> Ident.Tvar varname, T_int.SInt) state

  let appformula_of pvar = function STATE state ->
    let sorts = List.map (fun _ -> T_int.SInt) state in
    let args = List.map (fun (_, term) -> !term) state in
    Formula.mk_atom
      (Atom.mk_app
         (Predicate.mk_var pvar sorts)
         args)

  let get varname = function STATE state ->
    !(List.assoc varname state)

  let mem varname = function STATE state ->
    List.exists (fun (varname', _) -> varname' = varname) state

  let of_inits inits =
    List.fold_left
      Init.update_state
      (STATE [])
      inits
end

module FunDecl : sig
  type t =
      FUN_NONDET of string * string list
    | FUN_VOID of string * string list * Statement.t

  val is_fun_nondet: t -> bool
  val is_fun_void: t -> bool

  val mk_fun_nondet: string -> string list -> t
  val mk_fun_void: string -> string list -> Statement.t -> t

  val let_fun_nondet: t -> string * string list
  val let_fun_void: t -> string * string list * Statement.t

  val get_funname: t -> string
  val get_params: t -> string list
  val find_fundecl: string -> t list -> t
end = struct
  type t =
      FUN_NONDET of string * string list
    | FUN_VOID of string * string list * Statement.t

  let is_fun_nondet = function FUN_NONDET _ -> true | _ -> false
  let is_fun_void = function FUN_VOID _ -> true | _ -> false

  let mk_fun_nondet funname params = FUN_NONDET (funname, params)
  let mk_fun_void funname params body = FUN_VOID (funname, params, body)

  let let_fun_nondet = function FUN_NONDET (funname, params) -> funname, params | _ -> assert false
  let let_fun_void = function FUN_VOID (funname, params, body) -> funname, params, body | _ -> assert false

  let get_funname = function
    | FUN_NONDET (funname, _)
    | FUN_VOID (funname, _, _)
      -> funname

  let get_params = function
    | FUN_NONDET (_, params)
    | FUN_VOID (_, params, _)
      -> params

  let find_fundecl funname fundecls =
    match List.find_opt (fun fundecl -> get_funname fundecl = funname) fundecls with
    | Some fundecl -> fundecl
    | None -> failwith @@ Printf.sprintf "function %s was not declared in this scope" funname
end

type c = Ctl.t * Declare.t list * Init.t list * Statement.t
