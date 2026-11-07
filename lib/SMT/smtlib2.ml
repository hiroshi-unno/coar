(* Parser for SmtLib2 *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* open Parsexp *)
module Sexp = Ppx_sexp_conv_lib.Sexp

(* An index of an indexed identifier or of a declaration -- a bit-vector width,
   an extract or extend bound, an arity, a cardinality -- read as a native int.
   It is necessarily small, but the input is a numeral of any length, so one
   beyond a native int is refused with what it was the index of, where
   [int_of_string] raised a bare [Failure "int_of_string"].  Everything
   [int_of_string] reads is read as before. *)
let index_numeral ~what s =
  match int_of_string_opt s with
  | Some n -> n
  | None ->
      failwith
        (sprintf "%s: %s is not a numeral that fits a native integer" what s)

let str_of_sort = function
  | T_int.SInt -> "Int"
  | T_real.SReal -> "Real"
  | T_bool.SBool -> "Bool"
  | T_string.SString -> "String"
  | s -> failwith ("[str_of_sort] unsupported sort: " ^ Term.str_of_sort s)

let str_of_fsym = function
  | FVar (x, _, _) -> Ident.name_of_tvar x
  | T_int.Int n -> Z.to_string n
  | T_int.Neg -> "-"
  | T_int.Abs -> "abs"
  | T_int.Add -> "+"
  | T_int.Sub -> "-"
  | T_int.Mul -> "*"
  (* SMT-LIB's [div]/[mod] are the *Euclidean* pair, so only a Euclidean
     symbol may be printed as them.  The QFL, pGCL and SGCL grammars build
     [Truncated] ones for `/` and `mod`, and this function's output goes to
     external solvers (PolyQEnt, OptiMathSAT), where the difference shows up on
     negative operands: truncated -7 div 2 = -3, Euclidean -7 div 2 = -4.
     Printing the wrong operator would hand the solver a different problem, so
     the other three modes are refused instead -- encoding them needs an [ite]
     on the signs, which is how the reverse direction is parsed.  No input in
     the benchmark corpus reaches this today. *)
  | T_int.Div Value.Euclidean -> "div"
  | T_int.Rem Value.Euclidean -> "mod"
  | T_int.Div _ ->
      failwith
        "[SMT printing] only Euclidean integer division has an SMT-LIB \
         operator; a truncated, flooring or ceiling one would need an ite on \
         the operand signs"
  | T_int.Rem _ ->
      failwith
        "[SMT printing] only Euclidean integer remainder has an SMT-LIB \
         operator; a truncated, flooring or ceiling one would need an ite on \
         the operand signs"
  (*| T_int.Power -> "pow"*)
  | T_real.Real r ->
      if true then
        if Z.equal (Q.den r) Z.one then Z.to_string (Q.num r)
        else if Z.equal (Q.num r) Z.zero then Z.to_string Z.zero
        else sprintf "(/ %s %s)" (Z.to_string (Q.num r)) (Z.to_string (Q.den r))
      else Q.to_string r
  | T_real.RNeg -> "-"
  (*| T_real.RAbs -> "rabs"*)
  | T_real.RAdd -> "+"
  | T_real.RSub -> "-"
  | T_real.RMul -> "*"
  | T_real.RDiv -> "/"
  (*| T_real.RPower -> "rpow"*)
  | T_irb.IntToReal -> "to_real"
  | T_irb.RealToInt -> "to_int"
  | fsym ->
      failwith
        (sprintf "[str_of_fsym] unsupported function symbol: %s"
           (Term.str_of_funsym fsym))

let str_of_psym = function
  | T_bool.Eq -> "="
  (*| T_bool.Neq -> "xor"*)
  | T_int.Leq | T_real.RLeq -> "<="
  | T_int.Geq | T_real.RGeq -> ">="
  | T_int.Lt | T_real.RLt -> "<"
  | T_int.Gt | T_real.RGt -> ">"
  | _ -> failwith "[str_of_psym] unsupported predicate symbol"

let rec str_of_term = function
  | Term.Var (x, _, _) -> Ident.name_of_tvar x
  | Term.FunApp (fsym, args, _) ->
      if List.is_empty args then str_of_fsym fsym
      else
        sprintf "(%s %s)" (str_of_fsym fsym)
          (String.concat_map_list ~sep:" " args ~f:str_of_term)
  | Term.LetTerm (_x, _, _t1, _t2, _) -> failwith "unsupported"

let str_of_atom = function
  | Atom.True _info -> "true"
  | Atom.False _info -> "false"
  | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _info) ->
      if T_irb.is_sint_sreal t1 then
        sprintf "(or (< %s %s) (> %s %s))" (str_of_term t1) (str_of_term t2)
          (str_of_term t1) (str_of_term t2)
      else sprintf "(not (= %s %s))" (str_of_term t1) (str_of_term t2)
  | Atom.App (Predicate.Psym psym, args, _info) ->
      if List.is_empty args then str_of_psym psym
      else
        sprintf "(%s %s)" (str_of_psym psym)
          (String.concat_map_list ~sep:" " args ~f:str_of_term)
  (* a predicate-variable application, or any atom that is not a theory symbol.
     This printer emits pure SMT-LIB with no unknowns, so the caller has handed
     it a problem it cannot print -- naming the atom beats an [assert] that
     names only a line *)
  | atom ->
      failwith
      @@ sprintf "[SMT printing] not a theory atom: %s" (Atom.str_of atom)

let str_of_formula =
  Formula.fold
    ~f:
      (object
         method fatom = str_of_atom
         method fand = sprintf "(and %s %s)"
         method for_ = sprintf "(or %s %s)"
         method fimply = sprintf "(=> %s %s)"
         method fiff = sprintf "(= %s %s)"
         method fxor = sprintf "(xor %s %s)"
         method fnot = sprintf "(not %s)"
         method fbind _ _ _ = failwith "unsupported"
         method fletrec _ _ = failwith "unsupported"
         method flet _ _ _ _ = failwith "unsupported"
      end)

(* Sort names that [sort_of_sexp] had to default to [Sort.SVar] because they were
   not in scope at the point of use, i.e. declared by neither [declare-forall-sort]
   nor [declare-sort]/[declare-datatypes], and not a parameter of the enclosing
   datatype declaration.  Reported at most once per name, and only in verbose mode. *)
let undeclared_sorts = Atomic.make Set.Poly.empty

let warn_undeclared_sort ~print name =
  let seen = Atomic.get undeclared_sorts in
  if not (Set.mem seen name) then (
    Atomic.set undeclared_sorts (Set.add seen name);
    print
    @@ lazy
         (sprintf
            "[warning] undeclared sort \"%s\" is defaulted to a sort variable; \
             if it is meant to be a datatype, its declaration must precede \
             this use"
            name))

(* Sort aliases belong to one input. A domain-local, dynamically scoped table
   also keeps a nested reader from overwriting its caller's definitions. *)
let sort_aliases_key :
    (string, Ident.svar list * Sort.t) Hashtbl.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> Hashtbl.Poly.create ())

let sort_aliases () = Stdlib.Domain.DLS.get sort_aliases_key

let with_sort_alias_scope f =
  let saved = sort_aliases () in
  Stdlib.Domain.DLS.set sort_aliases_key (Hashtbl.Poly.create ());
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set sort_aliases_key saved)
    f

(* One declaration contract for aliases and both datatype syntaxes.
   These names are the theory sort constructors reserved by this reader. *)
let theory_sort_names =
  [ "Int"; "Real"; "Bool"; "String"; "Array"; "Seq"; "RegEx"; "BitVec" ]

let sort_parameters_of_sexp ~what params =
  let ps =
    List.map params ~f:(function
      | Sexp.Atom name -> Ident.Svar name
      | sexp ->
          failwith
          @@ sprintf "[%s] invalid parameter: %s" what
          @@ Sexp.to_string_hum sexp)
  in
  if List.contains_dup ps ~compare:Stdlib.compare then
    failwith @@ sprintf "[%s] duplicate sort parameter" what;
  List.iter ps ~f:(fun p ->
      if List.mem theory_sort_names (Ident.name_of_svar p) ~equal:String.equal
      then
        failwith @@ sprintf "[%s] a theory sort cannot be a sort parameter" what);
  ps

let is_local_sort_parameter params name =
  match params with
  | None -> false
  | Some params ->
      List.mem params (Sort.SVar (Ident.Svar name)) ~equal:Stdlib.( = )

let rec sort_of_sexp ~print uni_sort dtenv params = function
  | Sexp.Atom "Int" -> T_int.SInt
  | Sexp.Atom "Real" -> T_real.SReal
  | Sexp.Atom "Bool" -> T_bool.SBool
  | Sexp.Atom "String" -> T_string.SString
  (* Local parameters shadow user-defined sort symbols. Alias bodies have
     already been resolved at their definition site, so this lookup cannot
     capture a free name hidden inside an alias. *)
  | Sexp.Atom name when is_local_sort_parameter params name ->
      Sort.SVar (Ident.Svar name)
  | Sexp.List (Sexp.Atom name :: _) when is_local_sort_parameter params name ->
      failwith
      @@ sprintf "[sort_of_sexp] sort parameter %s cannot take arguments" name
  | Sexp.Atom name when Hashtbl.mem (sort_aliases ()) name -> (
      match Hashtbl.find_exn (sort_aliases ()) name with
      | [], body -> body
      | ps, _ ->
          failwith
          @@ sprintf "[define-sort] %s expects %d sort argument(s)" name
               (List.length ps))
  | Sexp.List (Sexp.Atom name :: args) when Hashtbl.mem (sort_aliases ()) name
    -> (
      let ps, body = Hashtbl.find_exn (sort_aliases ()) name in
      match List.zip ps args with
      | Ok subst ->
          Term.subst_sorts_sort
            (Map.Poly.of_alist_exn
               (List.map subst ~f:(fun (p, arg) ->
                    (p, sort_of_sexp ~print uni_sort dtenv params arg))))
            body
      | Unequal_lengths ->
          failwith
          @@ sprintf "[define-sort] %s expects %d sort argument(s), got %d" name
               (List.length ps) (List.length args))
  | Sexp.List [ Sexp.Atom "_"; Sexp.Atom "BitVec"; Sexp.Atom size ] ->
      T_bv.SBV (Some (index_numeral ~what:"(_ BitVec n)" size))
  | Sexp.List [ Sexp.Atom "Array"; s1; s2 ] ->
      T_array.mk_array_sort
        (sort_of_sexp ~print uni_sort dtenv params s1)
        (sort_of_sexp ~print uni_sort dtenv params s2)
  | Sexp.List [ Sexp.Atom "Seq"; se ] ->
      T_seq.mk_seq_sort (sort_of_sexp ~print uni_sort dtenv params se)
  | Sexp.List [ Sexp.Atom "RegEx"; Sexp.Atom "String" ] -> T_regex.SRegEx
  | Sexp.List (Sexp.Atom name :: args) as sexp -> (
      match DTEnv.look_up_dt dtenv name with
      | Some dt ->
          (* Applied and nullary uninterpreted declarations have the same
             representation; datatype display names are not sort identities. *)
          Datatype.sort_of
            (Datatype.update_params (Datatype.fresh_of dt)
            @@ List.map args ~f:(sort_of_sexp ~print uni_sort dtenv params))
      | None ->
          failwith
          @@ sprintf "[sort_of_sexp] unknown sort: %s" (Sexp.to_string sexp))
  | Sexp.Atom name -> (
      print @@ lazy (sprintf "[sort_of_sexp] %s" name);
      match DTEnv.look_up_dt dtenv name with
      | Some dt ->
          if
            (not (Datatype.is_alias dt))
            && not (List.is_empty (Datatype.params_of dt))
          then
            failwith
            @@ sprintf
                 "[sort_of_sexp] sort constructor %s expects %d sort \
                  argument(s), got 0"
                 name
                 (List.length (Datatype.params_of dt))
          else Datatype.sort_of @@ Datatype.fresh_of dt
      | None -> (
          if Set.mem uni_sort (Sort.SVar (Ident.Svar name)) then
            Sort.SVar (Ident.Svar name)
          else
            match params with
            | None ->
                (* SMT-LIB requires declaration before use.  Defaulting an
                   unknown name to a sort variable (as this parser once did)
                   let a datatype used before its declare-datatypes be read
                   as an uninterpreted sort and fail later inside Z3 with a
                   sort mismatch.  An ill-formed input (z3 and cvc5 reject it
                   too), so refused in one line rather than raised as an
                   internal failure printed with a backtrace. *)
                Common.Refusal.refuse
                  "[sort_of_sexp] undeclared sort \"%s\": declare it \
                   (declare-sort/declare-datatypes, or declare-forall-sort for \
                   a sort variable) before its first use"
                  name
            | Some _ -> failwith @@ sprintf "%s is not defined" name))
  | sexp ->
      failwith
      @@ sprintf "[sort_of_sexp] unknown sort: %s" (Sexp.to_string sexp)

(* Resolve scoped term bindings before constructor names. A qualification fixes
   a result sort, not a cast: a bound value must already have that sort. A
   constructor instead selects the annotated datatype instance and retains its
   specialized argument rank for type inference. *)
let qualified_identifier ~print ~term_of_sexp (envs : Problem.envs) name sort
    args =
  let result = sort_of_sexp ~print envs.uni_sort envs.dtenv None sort in
  let x = Ident.Tvar name in
  if
    Map.Poly.mem envs.uni_senv x
    || Map.Poly.mem envs.exi_senv x
    || Map.Poly.mem envs.fenv x
  then
    let term =
      term_of_sexp
        (if List.is_empty args then Sexp.Atom name
         else Sexp.List (Sexp.Atom name :: args))
    in
    if Stdlib.(Term.sort_of term = result) then term
    else
      failwith
      @@ sprintf
           "[qualified identifier] %s does not have the annotated result sort \
            %s"
           name (Sexp.to_string_hum sort)
  else
    let dt =
      match result with
      | T_dt.SDT dt -> dt
      | _ ->
          failwith
          @@ sprintf "[qualified constructor] %s is not a datatype result sort"
               (Sexp.to_string_hum sort)
    in
    let cons =
      match Datatype.look_up_cons dt name with
      | Some cons -> cons
      | None ->
          failwith
          @@ sprintf "[qualified constructor] %s is not a constructor of %s"
               name (Sexp.to_string_hum sort)
    in
    let arity = List.length (Datatype.sels_of_cons cons) in
    if List.length args <> arity then
      failwith
      @@ sprintf
           "[qualified constructor] %s expects %d term argument(s), got %d" name
           arity (List.length args);
    T_dt.mk_cons dt name (List.map args ~f:term_of_sexp)

(* Tester indices name constructors, independently of term-variable bindings.
   Bare indices need fresh rank parameters per occurrence. The supported explicit
   constructor signature instead fixes its owner and complete argument rank. *)
let datatype_tester ~print (envs : Problem.envs) constructor term =
  let dt, name =
    match constructor with
    | Sexp.Atom name -> (
        match DTEnv.look_up_func envs.dtenv name with
        | Some (dt, Datatype.FCons _) -> (Datatype.fresh_of dt, name)
        | _ ->
            failwith @@ sprintf "[datatype tester] %s is not a constructor" name
        )
    | Sexp.List [ Sexp.Atom name; Sexp.List arguments; result ] ->
        let dt =
          match sort_of_sexp ~print envs.uni_sort envs.dtenv None result with
          | T_dt.SDT dt -> dt
          | _ ->
              failwith "[datatype tester] constructor result is not a datatype"
        in
        let cons =
          match Datatype.look_up_cons dt name with
          | Some cons -> cons
          | None ->
              failwith
              @@ sprintf "[datatype tester] %s is not a constructor of %s" name
                   (Sexp.to_string_hum result)
        in
        let arguments =
          List.map arguments
            ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
        in
        if not Stdlib.(arguments = Datatype.sorts_of_cons dt cons) then
          failwith
          @@ sprintf
               "[datatype tester] %s has an incompatible constructor argument \
                rank"
               name;
        (dt, name)
    | _ -> failwith "[datatype tester] invalid constructor index"
  in
  T_dt.mk_is_cons dt name term

let bind_of_sexp ~print uni_sort dtenv = function
  | Sexp.List [ Sexp.Atom var; sort ] ->
      (Ident.Tvar var, sort_of_sexp ~print uni_sort dtenv None sort)
  | sexp ->
      failwith
      @@ sprintf "[bind_of_sexp] unknown bind: %s" (Sexp.to_string sexp)

(* Rename only occurrences belonging to an enclosing term binder, before
   expanding definitions. Renaming the parsed AST would also rename free names
   copied from an earlier definition, which belong to its definition site.
   Sorts, indexed identifiers and attributes are not term-variable occurrences;
   nested binders hide their names, and parallel let RHSs use the outer scope. *)
(* Source-only ranks for deciding whether an atom pattern is a constructor
   of this scrutinee, rather than a variable.  Unknown ranks stay unknown;
   constructor names from other datatypes do not determine this decision. *)
let match_source_sort (envs : Problem.envs) renaming = function
  | Sexp.Atom name -> (
      let var = Ident.Tvar name in
      let var = Option.value ~default:var (Map.Poly.find renaming var) in
      match Map.Poly.find envs.uni_senv var with
      | Some sort -> Some sort
      | None -> (
          match Map.Poly.find envs.fenv var with
          | Some ([], sort, _, _, _) -> Some sort
          | _ -> (
              match Map.Poly.find envs.exi_senv var with
              | Some sort -> (
                  match Sort.args_ret_of sort with
                  | [], result -> Some result
                  | _ -> None)
              | None -> (
                  match DTEnv.look_up_func envs.dtenv name with
                  | Some (dt, Datatype.FCons _) -> Some (T_dt.SDT dt)
                  | _ -> None))))
  | Sexp.List [ Sexp.Atom "as"; _; sort ] ->
      Some
        (sort_of_sexp ~print:(fun _ -> ()) envs.uni_sort envs.dtenv None sort)
  | Sexp.List (Sexp.Atom name :: _)
    when not (Map.Poly.mem envs.uni_senv (Ident.Tvar name)) -> (
      match DTEnv.look_up_func envs.dtenv name with
      | Some (dt, Datatype.FCons _) -> Some (T_dt.SDT dt)
      | _ -> None)
  | _ -> None

let match_scope_params (envs : Problem.envs) params =
  let uni_senv =
    List.fold params ~init:envs.uni_senv ~f:(fun senv param ->
        let var, sort =
          bind_of_sexp ~print:(fun _ -> ()) envs.uni_sort envs.dtenv param
        in
        Map.Poly.set senv ~key:var ~data:sort)
  in
  { envs with uni_senv }

let match_scope_bindings (envs : Problem.envs) renaming bindings =
  let uni_senv =
    List.fold bindings ~init:envs.uni_senv ~f:(fun senv -> function
      | Sexp.List [ Sexp.Atom name; rhs ] ->
          let sort =
            Option.value
              (match_source_sort envs renaming rhs)
              ~default:(Sort.mk_fresh_svar ())
          in
          Map.Poly.set senv ~key:(Ident.Tvar name) ~data:sort
      | _ -> senv)
  in
  { envs with uni_senv }

let match_scope_names (envs : Problem.envs) names =
  let uni_senv =
    List.fold names ~init:envs.uni_senv ~f:(fun senv -> function
      | Sexp.List [ Sexp.Atom name ] ->
          Map.Poly.set senv ~key:(Ident.Tvar name) ~data:(Sort.mk_fresh_svar ())
      | _ -> senv)
  in
  { envs with uni_senv }

let rec rename_bound_occurrences (envs : Problem.envs) renaming sexp =
  let without_bound_names bindings =
    List.fold bindings ~init:renaming ~f:(fun renaming -> function
      | Sexp.List (Sexp.Atom name :: _) ->
          Map.Poly.remove renaming (Ident.Tvar name)
      | _ -> renaming)
  in
  if Map.Poly.is_empty renaming then sexp
  else
    match sexp with
    | Sexp.Atom name -> (
        match Map.Poly.find renaming (Ident.Tvar name) with
        | Some name -> Sexp.Atom (Ident.name_of_tvar name)
        | None -> sexp)
    | Sexp.List
        [
          Sexp.Atom (("forall" | "exists" | "lambda") as binder);
          Sexp.List params;
          body;
        ] ->
        Sexp.List
          [
            Sexp.Atom binder;
            Sexp.List params;
            rename_bound_occurrences
              (match_scope_params envs params)
              (without_bound_names params)
              body;
          ]
    | Sexp.List
        [ Sexp.Atom (("let" | "random") as binder); Sexp.List bindings; body ]
      ->
        let bindings' =
          List.map bindings ~f:(function
            | Sexp.List [ name; rhs ] ->
                Sexp.List [ name; rename_bound_occurrences envs renaming rhs ]
            | binding -> binding)
        in
        Sexp.List
          [
            Sexp.Atom binder;
            Sexp.List bindings';
            rename_bound_occurrences
              (match_scope_bindings envs renaming bindings)
              (without_bound_names bindings)
              body;
          ]
    | Sexp.List [ Sexp.Atom "match"; scrut; Sexp.List cases ] ->
        (* a case's pattern variables are binders of its body; the pattern
           itself names a constructor and its fields and is left as written *)
        let pattern_names = function
          | Sexp.Atom "_" -> []
          | Sexp.Atom name when Map.Poly.mem renaming (Ident.Tvar name) -> (
              match match_source_sort envs renaming scrut with
              | Some (T_dt.SDT dt) -> (
                  match Datatype.look_up_cons dt name with
                  | Some _ -> []
                  | None -> [ Sexp.List [ Sexp.Atom name ] ])
              | Some (Sort.SVar _) | None ->
                  Common.Refusal.refuse
                    "[match] cannot resolve a shadowed atom pattern's datatype"
              | Some _ -> [ Sexp.List [ Sexp.Atom name ] ])
          | Sexp.Atom name -> [ Sexp.List [ Sexp.Atom name ] ]
          | Sexp.List (_ :: fields) ->
              List.map fields ~f:(fun field -> Sexp.List [ field ])
          | Sexp.List [] -> []
        in
        Sexp.List
          [
            Sexp.Atom "match";
            rename_bound_occurrences envs renaming scrut;
            Sexp.List
              (List.map cases ~f:(function
                | Sexp.List [ pattern; body ] ->
                    Sexp.List
                      [
                        pattern;
                        rename_bound_occurrences
                          (match_scope_names envs (pattern_names pattern))
                          (without_bound_names (pattern_names pattern))
                          body;
                      ]
                | case -> case));
          ]
    | Sexp.List [ Sexp.Atom "as"; identifier; sort ] ->
        Sexp.List
          [
            Sexp.Atom "as";
            rename_bound_occurrences envs renaming identifier;
            sort;
          ]
    | Sexp.List (Sexp.Atom "_" :: _) -> sexp
    | Sexp.List (Sexp.Atom "!" :: term :: attributes) ->
        Sexp.List
          (Sexp.Atom "!"
          :: rename_bound_occurrences envs renaming term
          :: attributes)
    | Sexp.List terms ->
        Sexp.List (List.map terms ~f:(rename_bound_occurrences envs renaming))

let is_function_name_bound (envs : Problem.envs) v =
  Map.Poly.mem envs.exi_senv v || Map.Poly.mem envs.fenv v

let fresh_binding_variable (envs : Problem.envs) =
  let rec draw () =
    let v = Ident.mk_fresh_tvar () in
    if Map.Poly.mem envs.uni_senv v || is_function_name_bound envs v then
      draw ()
    else v
  in
  draw ()

(* The parameters of one binder: the enclosing scope extended with them, the
   binder's own list, and the renaming that shadowing forced.

   Two different things used to be one.  The same name twice in ONE binding list
   is illegal and stays an error; a nested binder reusing an outer binder's name
   is ordinary SMT-LIB, the occurrence referring to the inner one, and used to
   be refused with "<name> is already bound" because the parameter was inserted
   into the enclosing scope with an insertion that rejects an existing key.

   Shadowing is handled by RENAMING the inner binder rather than by letting two
   binders share a name: several passes downstream -- renaming, skolemization
   and the prenexing helpers -- assume their input is alpha-converted, so a
   nested binder with its parent's name is not a value to hand them.  The body
   is renamed in the source before definitions are expanded, preserving the free
   names of those definitions. A fresh name is drawn only where shadowing
   actually happens, because drawing one moves every generated name after it.

   The sort is read *outside* the guard below, and only the insertions are
   guarded.  Reading it inside meant that any failure of the sort reader was
   reported as a repeated binder: a binder whose sort has no case here -- a
   function sort such as [((Int) Int)], which is not first-order and cannot be
   written in SMT-LIB -- said "<name> is already bound", a claim about the name
   that sent the reader looking for a duplicate that was not there. *)
let of_params ?(is_taken = fun _ -> false) ~print uni_senv sexps uni_sort dtenv
    =
  let uni_senv, params, renaming, _ =
    List.fold (List.rev sexps)
      ~init:(uni_senv, Map.Poly.empty, Map.Poly.empty, Set.Poly.empty)
      ~f:(fun (uni_senv, acc, renaming, seen) -> function
      | Sexp.List [ Sexp.Atom name; sort ] ->
          let sort = sort_of_sexp ~print uni_sort dtenv None sort in
          let v = Ident.Tvar name in
          if Set.mem seen v then
            failwith @@ name ^ " is bound twice by the same binder"
          else
            let v' =
              if Map.Poly.mem uni_senv v || is_taken v then
                let rec draw () =
                  let v' = Ident.mk_fresh_tvar () in
                  if Map.Poly.mem uni_senv v' || is_taken v' then draw ()
                  else v'
                in
                draw ()
              else v
            in
            ( Map.Poly.set uni_senv ~key:v' ~data:sort,
              Map.Poly.add_exn acc ~key:v' ~data:sort,
              (if Stdlib.(v' = v) then renaming
               else Map.Poly.set renaming ~key:v ~data:(v', sort)),
              Set.add seen v )
      | t -> failwith @@ "invalid param: " ^ Sexp.to_string t)
  in
  (uni_senv, params, renaming)

(* [re.none] is the Unicode Strings theory's name for the empty language;
   [re.empty] and [re.nostr] are z3's own spellings, which cvc5 refuses with a
   parse error, so the portable one has to be here and the other two are kept
   because shipped input uses them. *)
(* One row per symbol, for the same reason the binary operators below have one:
   two lists -- is it one of these, and what does it build -- are two places to
   remember a symbol, and a symbol added to one and forgotten in the other is
   either accepted and then raises, or refused although the constructor is right
   there.  [of_alist_exn] is what says a name may appear once. *)
let con_table : (string * Term.t) list =
  [
    ("true", T_bool.mk_true ());
    ("false", T_bool.mk_false ());
    ("re.all", T_regex.mk_full ());
    (* the language of the one-character strings, not of every string *)
    ("re.allchar", T_regex.mk_allchar ());
    (* [re.none] is the Unicode Strings theory's name for the empty language;
       [re.empty] and [re.nostr] are z3's own spellings, which cvc5 refuses with
       a parse error, so the portable one has to be here and the other two are
       kept because shipped input uses them *)
    ("re.none", T_regex.mk_empty ());
    ("re.empty", T_regex.mk_empty ());
    ("re.nostr", T_regex.mk_empty ());
  ]

let pred_sym1_table : (string * (?info:info -> Term.t -> Atom.t)) list =
  [ ("is_int", T_irb.mk_is_int) ]

let fun_sym1_table : (string * (?info:info -> Term.t -> Term.t)) list =
  let bv_of_arg f ?info t =
    f ?info ~size:(match Term.sort_of t with T_bv.SBV s -> s | _ -> None) t
  in
  [
    ("-", T_num.mk_nneg);
    (* the Ints theory declares [(abs Int Int)]; the Reals theory has no [abs],
       so this is the integer one and a Real operand is a sort error (z3 also
       accepts a Real operand, which the standard does not declare) *)
    ("abs", T_int.mk_abs);
    ("to_real", T_irb.mk_int_to_real);
    ("to_int", T_irb.mk_real_to_int);
    ("bv_to_uint", T_irb.mk_bv_to_int ~size:None ~signed:(Some false));
    ("ubv_to_int", T_irb.mk_bv_to_int ~size:None ~signed:(Some false));
    (* [bv2nat] is z3's and cvc5's older name for [ubv_to_int] *)
    ("bv2nat", T_irb.mk_bv_to_int ~size:None ~signed:(Some false));
    ("bv_to_sint", T_irb.mk_bv_to_int ~size:None ~signed:(Some true));
    ("sbv_to_int", T_irb.mk_bv_to_int ~size:None ~signed:(Some true));
    ("bvnot", bv_of_arg T_bv.mk_bvnot);
    ("bvneg", bv_of_arg T_bv.mk_bvneg);
    (* [str.to_re] is the Unicode Strings theory's name; [str.to.re] is z3's
       older one, which cvc5 refuses *)
    ("str.to_re", T_regex.mk_str_to_re);
    ("str.to.re", T_regex.mk_str_to_re);
    ("re.comp", T_regex.mk_complement);
    ("re.*", T_regex.mk_star);
    ("re.+", T_regex.mk_plus);
    ("re.opt", T_regex.mk_opt);
  ]

let con_map = Map.Poly.of_alist_exn con_table
let pred_sym1_map = Map.Poly.of_alist_exn pred_sym1_table
let fun_sym1_map = Map.Poly.of_alist_exn fun_sym1_table
let is_con op = Map.Poly.mem con_map op
let is_pred_sym1 op = Map.Poly.mem pred_sym1_map op
let is_fun_sym1 op = Map.Poly.mem fun_sym1_map op

let of_con op =
  match Map.Poly.find con_map op with
  | Some t -> t
  | None -> failwith @@ "parse error : " ^ op ^ " is not a constant symbol"

let of_pred_sym1 op =
  match Map.Poly.find pred_sym1_map op with
  | Some f -> f
  | None ->
      failwith @@ "parse error : " ^ op ^ " is not a unary predicate symbol"

let of_fun_sym1 op =
  match Map.Poly.find fun_sym1_map op with
  | Some f -> f
  | None ->
      failwith @@ "parse error : " ^ op ^ " is not a unary function symbol"

(* SMT-LIB gives each operator an arity rule in its theory declaration, and a
   reader that takes them all as binary refuses ordinary input: [(= 1 1 1)],
   [(< 1 2 3)], [(- 9 3 2)] and [(=> a b c)] are all standard and were answered
   with "<op> is not bound".

   The rule is a property of the *declaration* and not of the operator's shape:
   the arithmetic comparisons are [:chainable] and the bit-vector comparisons of
   the same shape are declared binary, so it cannot be guessed and has to be
   written out per operator.  It used to be spread over six lists -- is it a
   predicate, what does it build, is it n-ary, and one list per annotation --
   and adding an operator meant remembering which of them it belonged in; what
   went wrong was exactly that, every operator being in the binary lists and
   none of the n-ary ones in the folds.  Each operator now has ONE row below
   carrying both its constructor and its annotation, so it is either declared
   with its rule or absent entirely, with no half-declared state in between. *)
type arity =
  | Binary  (** exactly two operands; an application to more is a parse error *)
  | Chainable
      (** [:chainable] -- the operands are compared in adjacent pairs and the
          results conjoined, so [(< 1 3 2)] is false *)
  | RightAssoc
      (** [:right-assoc] -- [(=> a b c)] is [(=> a (=> b c))]. The direction is
          load bearing: [(=> false true false)] is true read this way and false
          read the other, and z3 and cvc5 both report the first *)
  | LeftAssoc
      (** [:left-assoc] -- folded from the first operand. A one-operand
          application is that operand, which is what these mean *)
  | LeftAssocUnary
      (** [:left-assoc] for an operator that also has a one-argument form of its
          own -- [(- x)] is negation -- so a lone operand must NOT be folded
          into the identity, and the fold is entered from three operands up *)

(* recover ~size from an operand's own sort, don't leave it None *)
let bv_size_of t1 t2 =
  match (Term.sort_of t1, Term.sort_of t2) with
  | T_bv.SBV (Some _ as size), _ | _, T_bv.SBV (Some _ as size) -> size
  | _ -> None

(* the binary predicate symbols: name, arity rule, constructor *)
let pred_sym2_table : (string * (arity * (Term.t -> Term.t -> Atom.t))) list =
  [
    ("=", (Chainable, fun t1 t2 -> T_bool.mk_eq t1 t2));
    ("<", (Chainable, fun t1 t2 -> T_num.mk_nlt t1 t2));
    (">", (Chainable, fun t1 t2 -> T_num.mk_ngt t1 t2));
    ("<=", (Chainable, fun t1 t2 -> T_num.mk_nleq t1 t2));
    (">=", (Chainable, fun t1 t2 -> T_num.mk_ngeq t1 t2));
    (* the FixedSizeBitVectors theory declares these binary, not chainable *)
    ( "bvule",
      (Binary, fun t1 t2 -> T_bv.mk_bvleq ~size:None ~signed:(Some false) t1 t2)
    );
    ( "bvsle",
      (Binary, fun t1 t2 -> T_bv.mk_bvleq ~size:None ~signed:(Some true) t1 t2)
    );
    ( "bvuge",
      (Binary, fun t1 t2 -> T_bv.mk_bvgeq ~size:None ~signed:(Some false) t1 t2)
    );
    ( "bvsge",
      (Binary, fun t1 t2 -> T_bv.mk_bvgeq ~size:None ~signed:(Some true) t1 t2)
    );
    ( "bvult",
      (Binary, fun t1 t2 -> T_bv.mk_bvlt ~size:None ~signed:(Some false) t1 t2)
    );
    ( "bvslt",
      (Binary, fun t1 t2 -> T_bv.mk_bvlt ~size:None ~signed:(Some true) t1 t2)
    );
    ( "bvugt",
      (Binary, fun t1 t2 -> T_bv.mk_bvgt ~size:None ~signed:(Some false) t1 t2)
    );
    ( "bvsgt",
      (Binary, fun t1 t2 -> T_bv.mk_bvgt ~size:None ~signed:(Some true) t1 t2)
    );
    (* [str.in_re] is the Unicode Strings theory's name; [str.in.re] is z3's
       older one, which cvc5 refuses *)
    ("str.in_re", (Binary, fun t1 t2 -> T_regex.mk_str_in_regexp t1 t2));
    ("str.in.re", (Binary, fun t1 t2 -> T_regex.mk_str_in_regexp t1 t2));
  ]

(* The connectives whose arity rule this reader derives from a table: their
   constructors build formulas rather than atoms or terms, so there is no
   constructor column.  [and], [or] and [xor] are not here because SMT-LIB
   declares them n-ary outright and the reader hands each its whole operand
   list; only [=>] needs a rule to fold by. *)
let connective_arity_table : (string * arity) list = [ ("=>", RightAssoc) ]

(* the binary function symbols: name, arity rule, constructor *)
let fun_sym2_table : (string * (arity * (Term.t -> Term.t -> Term.t))) list =
  let bv f t1 t2 = f ?info:(Some Dummy) ~size:(bv_size_of t1 t2) t1 t2 in
  let bv_signed f signed t1 t2 =
    f ?info:(Some Dummy) ~size:(bv_size_of t1 t2) ~signed t1 t2
  in
  [
    ("+", (LeftAssoc, T_num.mk_nadd ~info:Dummy));
    ("*", (LeftAssoc, T_num.mk_nmul ~info:Dummy));
    ("-", (LeftAssocUnary, T_num.mk_nsub ~info:Dummy));
    ("/", (LeftAssocUnary, T_real.mk_rdiv ~info:Dummy));
    ("div", (LeftAssocUnary, T_int.mk_div Value.Euclidean));
    ("mod", (Binary, T_int.mk_rem Value.Euclidean));
    ( "rem",
      ( Binary,
        (* Z3's rem takes the sign of the divisor
           (https://github.com/Z3Prover/z3/issues/6462); no Value.modulo
           expresses it, so build the same ite the Z3 decoder does. *)
        fun t1 t2 ->
          let m = T_int.mk_rem Value.Euclidean t1 t2 in
          (* sort-generic comparison: the divisor's sort is still to be
             inferred *)
          T_bool.mk_if_then_else
            (T_bool.of_atom @@ T_num.mk_ngeq t2 (T_num.mk_value "0"))
            m (T_int.mk_neg m) ) );
    ("^", (Binary, T_num.mk_npower ~info:Dummy));
    ("re.++", (LeftAssoc, T_regex.mk_concat ~info:Dummy));
    (* the Unicode Strings theory declares both [:left-assoc], so
       [(re.union r1 r2 r3)] is standard *)
    ("re.union", (LeftAssoc, T_regex.mk_union ~info:Dummy));
    ("re.inter", (LeftAssoc, T_regex.mk_inter ~info:Dummy));
    ("bvand", (LeftAssoc, bv T_bv.mk_bvand));
    ("bvor", (LeftAssoc, bv T_bv.mk_bvor));
    ("bvxor", (LeftAssoc, bv T_bv.mk_bvxor));
    ("bvadd", (LeftAssoc, bv T_bv.mk_bvadd));
    ("bvmul", (LeftAssoc, bv T_bv.mk_bvmul));
    ("bvnand", (Binary, bv T_bv.mk_bvnand));
    ("bvnor", (Binary, bv T_bv.mk_bvnor));
    ("bvxnor", (Binary, bv T_bv.mk_bvxnor));
    ("bvsub", (Binary, bv T_bv.mk_bvsub));
    ("bvudiv", (Binary, bv_signed T_bv.mk_bvdiv (Some false)));
    ("bvudiv_i", (Binary, bv_signed T_bv.mk_bvdiv (Some false)));
    ("bvsdiv", (Binary, bv_signed T_bv.mk_bvdiv (Some true)));
    ("bvsdiv_i", (Binary, bv_signed T_bv.mk_bvdiv (Some true)));
    ("bvurem", (Binary, bv_signed T_bv.mk_bvrem (Some false)));
    ("bvurem_i", (Binary, bv_signed T_bv.mk_bvrem (Some false)));
    ("bvsrem", (Binary, bv_signed T_bv.mk_bvrem (Some true)));
    ("bvsrem_i", (Binary, bv_signed T_bv.mk_bvrem (Some true)));
    ("bvsmod", (Binary, bv T_bv.mk_bvsmod));
    ("bvsmod_i", (Binary, bv T_bv.mk_bvsmod));
    ("bvshl", (Binary, bv T_bv.mk_bvshl));
    ("bvlshr", (Binary, bv T_bv.mk_bvlshr));
    ("bvashr", (Binary, bv T_bv.mk_bvashr));
    ( "concat",
      ( LeftAssoc,
        fun t1 t2 ->
          let size_of t =
            match Term.sort_of t with T_bv.SBV s -> s | _ -> None
          in
          T_bv.mk_bvconcat ~info:Dummy ~size1:(size_of t1) ~size2:(size_of t2)
            t1 t2 ) );
    ( "bvcomp",
      ( Binary,
        fun t1 t2 ->
          T_bool.ifte (Formula.eq t1 t2)
            (T_bv.mk_bvnum ~size:(Some 1) Z.one)
            (T_bv.mk_bvnum ~size:(Some 1) Z.zero) ) );
  ]

(* A table is the only declaration of an operator, so a name may appear in one
   of them exactly once; [of_alist_exn] is what says so. *)
let pred_sym2_map = Map.Poly.of_alist_exn pred_sym2_table
let fun_sym2_map = Map.Poly.of_alist_exn fun_sym2_table
let connective_arity_map = Map.Poly.of_alist_exn connective_arity_table
let is_pred_sym2 op = Map.Poly.mem pred_sym2_map op
let is_fun_sym2 op = Map.Poly.mem fun_sym2_map op

let of_pred_sym2 op =
  match Map.Poly.find pred_sym2_map op with
  | Some (_, f) -> f
  | None ->
      failwith @@ "parse error : " ^ op ^ " is not a binary predicate symbol"

let of_fun_sym2 op =
  match Map.Poly.find fun_sym2_map op with
  | Some (_, f) -> f
  | None ->
      failwith @@ "parse error : " ^ op ^ " is not a binary function symbol"

let arity_of op =
  match Map.Poly.find pred_sym2_map op with
  | Some (ar, _) -> Some ar
  | None -> (
      match Map.Poly.find fun_sym2_map op with
      | Some (ar, _) -> Some ar
      | None -> Map.Poly.find connective_arity_map op)

let arity_is op ar = Stdlib.(Some ar = arity_of op)
let is_chainable op = arity_is op Chainable
let is_right_assoc op = arity_is op RightAssoc
let is_left_assoc2 op = arity_is op LeftAssocUnary
let allow_mult_args op = arity_is op LeftAssoc

(* define-fun bodies are inlined by capture-avoiding substitution.
   Refresh their quantifier/let binders too: downstream shadow-only traversals
   require alpha-converted input. This protects actual arguments from the
   definition's binders; source renaming separately protects a definition's
   free globals from the caller's binders: with a global x, g() = x and
   f(x) = g would otherwise become f(x) = x. *)
let refresh_binders_formula phi =
  Formula.aconv_tvar @@ Formula.alpha_rename_let phi

let refresh_binders_term t = Term.aconv_tvar @@ Term.alpha_rename_let t

(* Whether inlining a [define-fun] call reads the fields of a constructor-application argument
   directly: where the body applies a selector to a formal whose actual argument is an
   application of that selector's constructor ([(mut_current v)] with [v := (mut a b)]), the
   inlined body has the field ([a]) in place of the read ([(mut_current (mut a b))]).  Process-wide,
   off by default (today's reading); PCSat's [reader.fold_inlined_selector_reads] turns it on before
   the input is read, and nothing turns it off again in the same process.

   Why: a definition whose body reads its formal several times and passes a constructor
   application built from those reads to the next definition doubles with every level when the
   argument is copied whole into each read.  A Rust front end's per-adaptor [completed] predicate
   does exactly this ([completed_j(x) = ... /\ completed_{j+1}(mut(proj (cur x), proj (fin x)))],
   [x] read four times per level): at sixteen levels the reading alone took 100 s and 3.3 GB to
   build definitions nothing applied, while with each read folded every level stays linear.

   Exact: [sel_i(C(t1, ..., tn)) = t_i] holds in every model of the datatype theory when [sel_i] is
   a selector of [C] (SMT-LIB 2.6, the datatype theory's selector axiom); a selector of another
   constructor is left as it is, since its value there is unspecified.  Only reads the
   substitution creates are folded -- a read the definition or its caller wrote out stays -- so the
   inlined body is the one read today with those redexes contracted, and nothing else changes. *)
let fold_inlined_selector_reads = ref false

(* the number of reads [fold_inlined_selector_reads] has folded in this process, for a test or a
   census asking where the switch acts without the phase-time account *)
let folded_reads = Atomic.make 0

(* the field a selector [fsym] reads of [arg], when [arg] is an application of the selector's
   own constructor; [None] for any other pair, a selector of another constructor included *)
let constructor_field fsym arg =
  match (fsym, arg) with
  | T_dt.DTSel (sel, dt, _), Term.FunApp (T_dt.DTCons (cons_name, _, _), ts, _)
    -> (
      match Datatype.look_up_cons dt cons_name with
      | None -> None
      | Some cons -> (
          match List.zip (Datatype.sels_of_cons cons) ts with
          | Ok pairs ->
              List.find_map pairs ~f:(fun (s, t) ->
                  if String.(Datatype.name_of_sel s = sel) then Some t else None)
          | Unequal_lengths -> None))
  | T_tuple.TupleSel (_, i), Term.FunApp (T_tuple.TupleCons _, ts, _) ->
      List.nth ts i
  | _ -> None

let is_constructor_app = function
  | Term.FunApp ((T_dt.DTCons _ | T_tuple.TupleCons _), _, _) -> true
  | _ -> false

(* [inline_with_reads_folded ~map_term ~names_of ~subst sub body] is [subst sub body] with every read
   [sel(x)] of a formal [x] whose actual [sub(x)] is an application of [sel]'s constructor replaced
   by that field, and reads of such a field folded in turn ([sel2(sel1(x))]), bottom-up.

   Assumes: [body]'s binders are fresh ([refresh_binders_*] ran), so a variable [x] in the domain of
   [sub] met inside [body] is the formal and never a bound variable spelt the same.  Guarantees: with
   [fold_inlined_selector_reads] off or no actual a constructor application, exactly [subst sub
   body]; otherwise [subst sub body] with only the redexes the substitution created contracted.  A
   folded read becomes a stand-in variable mapped to its field in the same simultaneous substitution,
   so the field -- a term of the caller, whose variables may be spelt like this definition's
   formals -- is never substituted into again. *)
let inline_with_reads_folded ~map_term ~names_of ~subst sub body =
  if
    (not !fold_inlined_selector_reads)
    || not (Map.Poly.exists sub ~f:is_constructor_app)
  then subst sub body
  else
    let extra = ref Map.Poly.empty in
    (* the stand-ins are named here rather than drawn from [Ident.mk_fresh_tvar], so that the
       names drawn after this reading are the ones today's reading draws: a stand-in never
       survives this call, and the name is kept apart from every name in the body and the
       formals. Nullary predicate names matter too: the final substitution can replace a
       Boolean predicate when a Boolean stand-in has the same spelling. *)
    let taken = lazy (Set.union (Map.key_set sub) (names_of body)) in
    let rec stand_in n =
      let z = Ident.Tvar (sprintf "#inline_read%d" n) in
      if Set.mem (Lazy.force taken) z || Map.Poly.mem !extra z then stand_in (n + 1)
      else z
    in
    let actual x =
      match Map.Poly.find sub x with
      | Some t -> Some t
      | None -> Map.Poly.find !extra x
    in
    let folded =
      map_term body ~f:(function
        | Term.FunApp (fsym, [ Term.Var (x, _, _) ], _) as t0 -> (
            match Option.bind (actual x) ~f:(constructor_field fsym) with
            | None -> t0
            | Some field ->
                let z = stand_in (Map.Poly.length !extra) in
                extra := Map.Poly.add_exn !extra ~key:z ~data:field;
                Term.mk_var z (Term.sort_of t0))
        | t -> t)
    in
    (* nothing folded: the body as given, not [map_term]'s rebuilding of it *)
    if Map.Poly.is_empty !extra then subst sub body
    else (
      (* the reads folded, as a row of the phase-time report: the trace of where it acts *)
      Common.PhaseTime.add_here "fold-selector-read" ~secs:0.
        ~count:(Map.Poly.length !extra);
      ignore (Atomic.fetch_and_add folded_reads (Map.Poly.length !extra) : int);
      subst
        (Map.Poly.merge_skewed sub !extra ~combine:(fun ~key:_ v _ -> v))
        folded)

(* An argument of a call that is about to be INLINED has to be reconciled with the
   formal parameter's sort.  A numeric literal is parsed as a value carrying a fresh
   sort variable and is settled by the whole-formula type inference that runs at the
   very end; a definition's body, on the other hand, was type-checked when it was
   declared, so its arithmetic is already Int- or Real-specific.  Inlining puts the
   second kind of term around the first, and the normalization that runs between the
   two -- before type inference gets its turn -- dispatches on the typed operation
   and refuses the untyped argument:
   [(define-fun f ((n Int)) Int (+ n 1)) (assert (= (f 2) 3))] raised
   "[int_monomials_of] not supported" where z3 and cvc5 answer sat.  Two things hid
   it: a call whose argument is a declared variable carries that variable's sort,
   and the same arithmetic written out in the assertion is typed by inference along
   with everything around it.

   The reconciliation is done by the type checker rather than by hand.  Substituting
   the argument's own top-level sort variable is not enough and looked as if it were
   until a test said otherwise: in [(f (+ 2 1))] the addition and each literal carry
   a DIFFERENT sort variable, and it is inference that unifies them.  So the
   argument is inferred against the formal as its expected sort, with the formal also
   the default for anything numeric left unresolved.  Only an argument that still
   has a sort variable in it is touched, so a fully typed one goes through
   untouched. *)
(* The sort variables that `declare-forall-sort` introduced: universally
   quantified sorts, which type inference must not bind as unification targets. *)
let rigid_of_scan uni_sort =
  Set.Poly.filter_map uni_sort ~f:(function Sort.SVar v -> Some v | _ -> None)

(* [rigid_of_scan], remembered for the last set it was asked about: the reader
   asks once per argument of every inlined definition call with the same set of
   universally quantified sorts, and on an input with a hundred such sorts and
   tens of thousands of calls the repeated filter was an eighth of the reading
   time.  A set is immutable, so physical identity is enough to reuse an
   answer. *)
let rigid_cache : (Sort.t Set.Poly.t * Ident.svar Set.Poly.t) option Atomic.t =
  Atomic.make None

let rigid_of uni_sort =
  match Atomic.get rigid_cache with
  | Some (s, r) when phys_equal s uni_sort -> r
  | _ ->
      let r = rigid_of_scan uni_sort in
      Atomic.set rigid_cache (Some (uni_sort, r));
      r

let with_formal_sort ~print ~rigid senv (_, formal) arg =
  (* [Term.svs_of] cannot answer "does this still have an unresolved sort", because
     it does not look inside a function symbol -- its application case carries the
     comment "fsym may contain sort variables?" and collects only the arguments --
     so a numeric value, which keeps its sort variable in the SYMBOL, contributes
     nothing to it.  Asking after the symbols directly is what works. *)
  let unresolved =
    Set.exists (Term.funsyms_of arg) ~f:(function
      | T_num.(
          ( Value _ | NNeg _ | NAdd _ | NSub _ | NMul _ | NDiv _ | NRem _
          | NPower _ )) ->
          true
      | _ -> false)
  in
  if not unresolved then arg
  else
    Typeinf.typeinf_term ~print ~to_sus:true ~rigid ~default:(Some formal) ~senv
      ~sort_opt:(Some formal) arg

(* The universal term variables (a [declare-forall-fun], a [declare-var]) that a recursive
   definition's body mentions, keyed by the definition's name, made explicit trailing parameters
   of the definition by [lift_universals]. The metadata belongs to the same
   reader environment as the definition, so a later independent read cannot
   change how an application in a retained environment is completed.

   Why: a universal is universal in every clause, and a clause's universals are renamed,
   quantified and instantiated clause by clause.  A recursive definition is kept in the function
   environment and handed to the SMT solver as one global definition, so a universal left free in
   its body becomes one fixed constant there, unrelated to the clause variable of the same name
   once the clause's variables are renamed or bound: a valid clause relating [f(s[0])] to a
   recursive count over [f] was refuted by a model choosing the constant apart from the clause's
   [f].  Passing the universal as an argument at every application is closure conversion; it
   makes the definition closed and keeps the application's meaning in every model. *)
(* [args] completed with the lifted universals of [name] when it has some and [args] supplies
   exactly the parameters the definition was written with; [args] unchanged otherwise. *)
let with_lifted_args (envs : Problem.envs) name (fargs : sort_env_list) args =
  match Map.Poly.find envs.lifted_universals (Ident.Tvar name) with
  | Some extra
    when List.length args + List.length extra = List.length fargs ->
      args @ List.map extra ~f:(Tuple2.uncurry Term.mk_var)
  | _ -> args

(* Closure conversion of a group of recursive definitions [(name, params, sort, body)], each
   body read with every name of the group bound to its written parameters.  Returns the group
   with every universal of [uni_senv] that occurs free in some body appended, in one fixed
   order, to every member's parameters, and every application of a member inside the bodies
   given those universals as the trailing arguments.  Each parameter added is named and sorted
   as the universal itself, so its occurrences in the bodies need no renaming.  An application
   of an earlier lifted definition already carries its universals (see [with_lifted_args]), so
   they are free here and lifted again: the closure is transitive.  Records the result in
   the returned metadata map. Refuses a group in which a member's own parameter is spelled like a
   universal another member mentions free, since the added parameter would collide with it. *)
let lift_universals (envs : Problem.envs) group =
  let uni_senv = envs.uni_senv in
  let lifted_universals =
    List.fold group ~init:envs.lifted_universals ~f:(fun map (n, _, _, _) ->
        Map.Poly.remove map (Ident.Tvar n))
  in
  let names =
    Set.Poly.of_list (List.map group ~f:(fun (n, _, _, _) -> Ident.Tvar n))
  in
  let extra =
    List.concat_map group ~f:(fun (_, (fargs : sort_env_list), _, body) ->
        let bound = Set.Poly.of_list (List.map fargs ~f:fst) in
        List.filter_map (Set.to_list (Term.tvs_of body)) ~f:(fun x ->
            if Set.mem bound x || Set.mem names x then None
            else Option.map (Map.Poly.find uni_senv x) ~f:(fun s -> (x, s))))
    |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) ->
           Ident.tvar_compare x y)
  in
  if List.is_empty extra then (group, lifted_universals)
  else (
    List.iter group ~f:(fun (n, (fargs : sort_env_list), _, _) ->
        match
          List.find extra ~f:(fun (x, _) ->
              List.exists fargs ~f:(fst >> Ident.tvar_equal x))
        with
        | Some (x, _) ->
            failwith
            @@ sprintf
                 "[define-fun-rec %s] a parameter is named like the universal %s another definition of its group mentions"
                 n (Ident.name_of_tvar x)
        | None -> ());
    let arity =
      Map.Poly.of_alist_exn
      @@ List.map group ~f:(fun (n, fargs, _, _) ->
          (Ident.Tvar n, List.length fargs))
    in
    let extra_sorts = List.map extra ~f:snd in
    let extra_args = List.map extra ~f:(Tuple2.uncurry Term.mk_var) in
    let close =
      Term.map_term true ~f:(function
        | Term.FunApp (FVar (n, sargs, sret), args, _)
          when Option.equal Int.equal (Map.Poly.find arity n) (Some (List.length args)) ->
            Term.mk_fvar_app n (sargs @ extra_sorts) sret (args @ extra_args)
        | t -> t)
    in
    let lifted_universals =
      List.fold group ~init:lifted_universals ~f:(fun map (n, _, _, _) ->
          Map.Poly.set map ~key:(Ident.Tvar n) ~data:extra)
    in
    ( List.map group ~f:(fun (n, fargs, sort, body) ->
          (n, fargs @ extra, sort, close body)),
      lifted_universals ))

(* Infer only a rank already forced by the operand, without defaulting a
   generic numeral. A compound Int expression otherwise still looks like a
   sort variable at this source boundary. Keep rigid source sorts rigid. *)
let source_numeric_rank ~print (envs : Problem.envs) term =
  match Term.sort_of term with
  | Sort.SVar _ ->
      let inferred =
        Typeinf.typeinf_term ~print ~default:None ~to_sus:true
          ~rigid:(rigid_of envs.uni_sort) ~senv:envs.uni_senv term
      in
      (match Term.sort_of inferred with
      | T_int.SInt | T_real.SReal -> inferred
      | _ -> term)
  | _ -> term

(* A source operator can require Real before a let-bound operand's rank is
   known. Keep that conversion separate from strict sort equality until the
   enclosing expression (including a definition's result) supplies its
   constraints. These private placeholders never enter a stored definition or
   the solver. Domain-local scope is restored on exceptions and nested reads. *)
let source_numeric_scope_key :
    Ident.tvar Set.Poly.t ref option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

(* Public reader entry points may be called by a diagnostic callback while
   another expression is being read. Isolate that input, then restore the
   caller's still-pending conversions. Recursive source parsing shares them. *)
let with_source_numeric_reader_scope f =
  let saved = Stdlib.Domain.DLS.get source_numeric_scope_key in
  Stdlib.Domain.DLS.set source_numeric_scope_key None;
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set source_numeric_scope_key saved)
    f

let with_source_numeric_scope ~print (envs : Problem.envs) ~constrs_of
    ~subst_sorts ~map_term f =
  match Stdlib.Domain.DLS.get source_numeric_scope_key with
  | Some _ -> f ()
  | None ->
      let pending = ref Set.Poly.empty in
      Stdlib.Domain.DLS.set source_numeric_scope_key (Some pending);
      Common.Timer.protect
        ~finally:(fun () -> Stdlib.Domain.DLS.set source_numeric_scope_key None)
        (fun () ->
          let root = f () in
          if Set.is_empty !pending then root
          else
            (* Speculative reader branches may have been discarded. Only
               placeholders in the returned tree contribute constraints, and
               their current signature retains any local rank substitution. *)
            let ranks = ref Set.Poly.empty in
            let live = ref false in
            let _ =
              map_term root ~f:(fun term ->
                  (match term with
                  | Term.FunApp (FVar (v, [ sort ], _), [ _ ], _)
                    when Set.mem !pending v ->
                      live := true;
                      ranks := Set.add !ranks sort
                  | _ -> ());
                  term)
            in
            if not !live then root
            else
              let numeric =
                Set.Poly.filter_map !ranks ~f:(function
                  | Sort.SVar svar -> Some (Typeinf.CNum svar)
                  | T_int.SInt | T_real.SReal -> None
                  | _ -> failwith "ill-sorted source numeric conversion")
              in
              let constrs = Set.union (constrs_of root) numeric in
              let rigid = rigid_of envs.uni_sort in
              let _, preliminary = Typeinf.solve ~print ~rigid constrs in
              (* Default only operands requiring conversion that are still
                 unresolved. Other generic numerals keep their usual policy. *)
              let defaults =
                Set.Poly.filter_map !ranks ~f:(fun sort ->
                    match Term.subst_sorts_sort preliminary sort with
                    | Sort.SVar _ as sort ->
                        Some (Typeinf.CEq (sort, T_real.SReal))
                    | _ -> None)
              in
              let _, substitution =
                Typeinf.solve ~print ~rigid (Set.union constrs defaults)
              in
              map_term (subst_sorts substitution root) ~f:(function
                | Term.FunApp (FVar (v, _, _), [ arg ], _)
                  when Set.mem !pending v -> (
                    match Term.sort_of arg with
                    | T_int.SInt -> T_irb.mk_int_to_real arg
                    | T_real.SReal -> arg
                    | _ -> failwith "ill-sorted source numeric conversion")
                | term -> term))

(* Reals_Ints operator sugar is an explicit Int-to-Real conversion, not a
   relaxation of core sort equality or of a user function's signature. *)
let source_numeric_pair ~print envs op t1 t2 =
  match op with
  | "+" | "-" | "*" | "/" | "=" | "<" | ">" | "<=" | ">=" ->
      let t1' = source_numeric_rank ~print envs t1 in
      let t2' = source_numeric_rank ~print envs t2 in
      let s1 = Term.sort_of t1' and s2 = Term.sort_of t2' in
      if String.equal op "/" || Stdlib.(s1 = T_real.SReal || s2 = T_real.SReal)
      then
        let promote t =
          match Term.sort_of t with
          | T_int.SInt -> T_irb.mk_int_to_real t
          | Sort.SVar _ as sort -> (
              match Stdlib.Domain.DLS.get source_numeric_scope_key with
              | None -> t
              | Some pending ->
                  let v = fresh_binding_variable envs in
                  pending := Set.add !pending v;
                  Term.mk_fvar_app v [ sort ] T_real.SReal [ t ])
          | _ -> t
        in
        (promote t1', promote t2')
      else (t1, t2)
  | _ -> (t1, t2)

let source_pred_sym2 ~print envs op t1 t2 =
  let t1, t2 = source_numeric_pair ~print envs op t1 t2 in
  of_pred_sym2 op t1 t2

let source_fun_sym2 ~print envs op t1 t2 =
  let t1, t2 = source_numeric_pair ~print envs op t1 t2 in
  of_fun_sym2 op t1 t2

(* SMT-LIB 2.6 [match] (the standard's term syntax, section 3.6.1):
   [(match t ((p_1 b_1) ... (p_n b_n)))] denotes [b_i] for the FIRST case whose
   pattern matches [t].  A pattern is a nullary constructor [C], a constructor
   applied to distinct variables [(C x_1 ... x_k)], which binds each [x_j] to the
   j-th field of [t], or a variable [x], which matches everything and binds the
   whole of [t].  The cases must be exhaustive; the standard requires it of the
   input, and both z3 and cvc5 reject a match that is not.

   The term language here has no match, so it is read as the testers and
   selectors it abbreviates: case [(C x_1 ... x_k) b] becomes [is-C t] guarding
   [b] with each [x_j] let-bound to [sel_j t].  That is exact because a selector
   is only read under the tester of its own constructor, where its value is
   fixed by the theory -- no selector is applied off its constructor, so no
   interpretation-dependent term is introduced.  Distinct constructors' testers
   are mutually exclusive, so only a variable case needs the earlier testers
   negated; a later case for a constructor already seen, and every case after a
   variable case, can never apply and is dropped.

   What is refused rather than guessed: a match with no exhaustive coverage
   (inventing a value for the missing constructors would decide what the
   standard leaves an error), a nested pattern, a repeated pattern variable, a
   constructor applied to the wrong number of fields, a constructor of another
   datatype, and a scrutinee of a non-datatype sort under a constructor
   pattern.  [_] as a pattern or a field is z3's wildcard (cvc5 rejects it); it
   is read as a variable that is never mentioned.

   [scrut] must already be a variable or a term that may be duplicated without
   changing the meaning: the caller let-binds anything else.  The result lists
   the reachable cases in order, each with its guard, the source names it binds
   and the terms they denote, and its body as source. *)
type match_guard =
  | Match_cons of string  (** [is-C] of the scrutinee *)
  | Match_default of string list
      (** every scrutinee not built by these (earlier) constructors *)

let match_cases (envs : Problem.envs) scrut cases =
  let refuse fmt = Common.Refusal.refuse ("[match] " ^^ fmt) in
  let dt =
    match Term.sort_of scrut with
    | T_dt.SDT dt -> Some dt
    | Sort.SVar _ ->
        (* a scrutinee whose sort is not yet inferred: a constructor named by
           a pattern fixes the datatype, with fresh sort parameters as every
           other constructor occurrence gets *)
        List.find_map cases ~f:(function
          | Sexp.List [ (Sexp.Atom name | Sexp.List (Sexp.Atom name :: _)); _ ]
            -> (
              match DTEnv.look_up_func envs.dtenv name with
              | Some (dt, Datatype.FCons _) -> Some (Datatype.fresh_of dt)
              | _ -> None)
          | _ -> None)
    | _ -> refuse "the matched term must have a datatype sort"
  in
  if Option.is_none dt then
    refuse "the matched term's datatype sort could not be established";
  let cons_of name =
    match dt with
    | Some dt -> Datatype.look_up_cons dt name
    | None -> None
  in
  let rec go seen acc = function
    | [] ->
        let covered =
          match dt with
          | Some dt ->
              List.for_all (Datatype.conses_of dt) ~f:(fun cons ->
                  List.mem seen (Datatype.name_of_cons cons) ~equal:String.equal)
          | None -> false
        in
        if not covered then
          refuse "the cases are not exhaustive: %s"
            (Sexp.to_string_hum (Sexp.List cases));
        List.rev acc
    | Sexp.List [ pattern; body ] :: rest -> (
        match pattern with
        | Sexp.Atom "_" -> List.rev ((Match_default seen, [], body) :: acc)
        | Sexp.Atom name -> (
            match cons_of name with
            | Some cons ->
                if not (List.is_empty (Datatype.sels_of_cons cons)) then
                  refuse "constructor %s has fields, which its pattern must name"
                    name;
                if List.mem seen name ~equal:String.equal then go seen acc rest
                else go (name :: seen) ((Match_cons name, [], body) :: acc) rest
            | None ->
                List.rev
                  ((Match_default seen, [ (Ident.Tvar name, scrut) ], body)
                  :: acc))
        | Sexp.List (Sexp.Atom name :: (_ :: _ as fields)) ->
            let dt, cons =
              match (dt, cons_of name) with
              | Some dt, Some cons -> (dt, cons)
              | _ ->
                  refuse "%s is not a constructor of the matched term's sort"
                    name
            in
            let sels = Datatype.sels_of_cons cons in
            if List.length fields <> List.length sels then
              refuse "constructor %s has %d field(s), its pattern names %d" name
                (List.length sels) (List.length fields);
            let fields =
              List.map fields ~f:(function
                | Sexp.Atom field -> field
                | field ->
                    refuse "a pattern field must be a variable, not %s"
                      (Sexp.to_string_hum field))
            in
            let named =
              List.filter fields ~f:(Fn.non (String.equal "_"))
            in
            if List.contains_dup named ~compare:String.compare then
              refuse "a variable is repeated in the pattern %s"
                (Sexp.to_string_hum pattern);
            if List.mem seen name ~equal:String.equal then go seen acc rest
            else
              let binds =
                List.filter_map (List.zip_exn fields sels) ~f:(fun (field, sel) ->
                    if String.equal field "_" then None
                    else
                      Some
                        ( Ident.Tvar field,
                          T_dt.mk_sel dt (Datatype.name_of_sel sel) scrut ))
              in
              go (name :: seen) ((Match_cons name, binds, body) :: acc) rest
        | _ ->
            refuse "unsupported pattern %s (patterns are not nested)"
              (Sexp.to_string_hum pattern))
    | case :: _ -> refuse "malformed case %s" (Sexp.to_string_hum case)
  in
  if List.is_empty cases then refuse "a match needs at least one case";
  let cases = go [] [] cases in
  (dt, cases)

(* The guard of one reachable case, as an atom set over the scrutinee. *)
let match_guard dt scrut = function
  | Match_cons name -> (
      match dt with
      | Some dt -> Formula.mk_atom (T_dt.mk_is_cons dt name scrut)
      | None -> assert false (* a constructor case fixes [dt] *))
  | Match_default seen -> (
      match dt with
      | Some dt ->
          Formula.and_of
          @@ List.map seen ~f:(fun name ->
              Formula.mk_atom (T_dt.mk_is_not_cons dt name scrut))
      | None -> Formula.mk_true ())

(* Bind one case's pattern variables around its body, as [let] does: a name
   that shadows an enclosing binder or a function is renamed apart in the
   source, keeping the result alpha-converted. *)
let match_case_scope (envs : Problem.envs) binds body =
  let renaming =
    Map.Poly.of_alist_exn
    @@ List.filter_map binds ~f:(fun (v, _) ->
        if Map.Poly.mem envs.uni_senv v || is_function_name_bound envs v then
          Some (v, fresh_binding_variable envs)
        else None)
  in
  let bound_name v = Option.value ~default:v (Map.Poly.find renaming v) in
  let binds =
    List.map binds ~f:(fun (v, def) -> (bound_name v, Term.sort_of def, def))
  in
  let uni_senv =
    List.fold binds ~init:envs.uni_senv ~f:(fun uni_senv (v, sort, _) ->
        Map.Poly.add_exn uni_senv ~key:v ~data:sort)
  in
  ({ envs with uni_senv }, binds,
   rename_bound_occurrences { envs with uni_senv } renaming body)

(* A scrutinee that is not a variable is let-bound to a fresh one, so the
   guards and selectors read it without copying it. *)
let match_scrutinee ~print (envs : Problem.envs) scrut =
  let scrut =
    let _, root_sort, constrs = Typeinf.cgen_term ~print envs.uni_senv scrut in
    let nums, substitution =
      Typeinf.solve ~print ~rigid:(rigid_of envs.uni_sort) constrs
    in
    (* A numeric rank can remain a sort variable without defaulting.  It is
       already known not to be a datatype, unlike an unconstrained rank. *)
    (match Term.subst_sorts_sort substitution root_sort with
    | Sort.SVar v when Set.mem nums v ->
        Common.Refusal.refuse
          "[match] the matched term must have a datatype sort"
    | _ -> ());
    Term.subst_sorts
      (Typeinf.elim_nums ~to_sus:true ~default:None nums substitution)
      scrut
  in
  match scrut with
  | Term.Var _ -> (scrut, None)
  | _ ->
      let v = fresh_binding_variable envs in
      let sort = Term.sort_of scrut in
      (Term.mk_var v sort, Some (v, sort, scrut))

(* Keep the datatype constraint even when the sole/last branch needs no
   tester and reads no fields.  Otherwise desugaring can erase the only
   constraint on a scrutinee whose source rank is still a sort variable. *)
let match_sort_binding envs scrut bound dt =
  match dt with
  | None -> assert false (* [match_cases] establishes the datatype *)
  | Some dt ->
      let sort = T_dt.SDT dt in
      Some
        (match bound with
        | Some (v, _, def) -> (v, sort, def)
        | None -> (fresh_binding_variable envs, sort, scrut))

(* A symbol that no declaration, definition, binder or datatype in scope names.
   z3 and cvc5 reject such an input ("unknown constant"), so it is refused as an
   ill-formed input in one sentence rather than raised as an internal failure,
   which the command-line entry would print as a backtrace.  The refusal is an
   ordinary exception: the reader's fallbacks that try another reading on any
   failure still catch it. *)
let refuse_unbound name =
  Common.Refusal.refuse
    "%s is not bound: no declaration or definition of this symbol is in scope"
    name

(* [-] directly followed by a digit starts a numeral or a decimal for z3 5.1.0
   and cvc5 1.4.2 ([-1], [-1.5]), so neither takes such a spelling for a
   symbol: declaring or binding it is an error ("symbol expected"), and the
   atom always denotes the negative number.  This reader does the same,
   although the SMT-LIB 2.6 grammar makes [-1] a simple symbol: the files
   written for those solvers, and the in-house CHC files writing [(> x -1)],
   mean the number.  A quoted [|-1|] is a symbol for both solvers; the lexer
   keeps its bars, so it never meets this test. *)
let is_negative_numeral_spelling name =
  String.length name >= 2 && Char.equal name.[0] '-' && Char.is_digit name.[1]

let refuse_numeral_symbol ~what name =
  Common.Refusal.refuse "[%s] symbol expected, but %s is a numeral" what name

(* What may be declared as a function or sort symbol: not a numeral spelling
   (above), and not a symbol beginning with [.] or [@], which SMT-LIB 2.6
   reserves for solver-generated names (cvc5 1.4.2 refuses their declaration,
   also when quoted; z3 5.1.0 accepts it).  [|@x|] and [@x] are one symbol in
   SMT-LIB 2.6, and the lexer strips the bars of such a quoted symbol, so both
   spellings are refused here. *)
let ensure_declarable_symbol ~what name =
  if is_negative_numeral_spelling name then refuse_numeral_symbol ~what name;
  if String.is_prefix name ~prefix:"." || String.is_prefix name ~prefix:"@"
  then
    Common.Refusal.refuse
      "[%s] cannot declare %s: symbols beginning with . or @ are reserved for \
       solvers in SMT-LIB"
      what name

(* Whether [name] is a term variable, a declared symbol or a defined function
   in scope: the three bindings [bound_symbol_term] reads. *)
let is_term_symbol_bound (envs : Problem.envs) name =
  let v = Ident.Tvar name in
  Map.Poly.mem envs.uni_senv v || Map.Poly.mem envs.exi_senv v
  || Map.Poly.mem envs.fenv v

(* The term a bare symbol denotes through its binding: a bound or universal
   variable, a declared constant, or a nullary definition (inlined when
   [inline]); a recursive definition applied to no written argument takes its
   lifted universals.  The innermost binding wins: variables before
   declarations before definitions.  [None] when no such binding exists;
   raises on a definition that takes arguments. *)
let bound_symbol_term ~inline (envs : Problem.envs) name =
  let v = Ident.Tvar name in
  match Map.Poly.find envs.uni_senv v with
  | Some sort -> Some (Term.mk_var v sort)
  | None -> (
      match Map.Poly.find envs.exi_senv v with
      | Some sort -> Some (Term.mk_var v sort)
      | None -> (
          match Map.Poly.find envs.fenv v with
          | Some ([], sret, t, false, _) ->
              Some (if inline then t else Term.mk_fvar_app v [] sret [])
          | Some (fargs, sret, _, true, _)
            when List.length (with_lifted_args envs name fargs [])
                 = List.length fargs ->
              Some
                (Term.mk_fvar_app v (List.map ~f:snd fargs) sret
                   (with_lifted_args envs name fargs []))
          | Some _ ->
              failwith
              @@ sprintf "[term] %s takes arguments and is applied to none" name
          | None -> None))

let rec of_formula ~print ~inline (envs : Problem.envs) phi =
  with_source_numeric_scope ~print envs
    ~constrs_of:(fun phi ->
      snd (Typeinf.cgen_formula ~print envs.uni_senv phi))
    ~subst_sorts:Formula.subst_sorts ~map_term:(fun root ~f -> Formula.map_term ~f root)
    (fun () -> of_formula_raw ~print ~inline envs phi)

and of_formula_raw ~print ~inline (envs : Problem.envs) phi =
  let open Formula in
  (fun ret ->
    print @@ lazy ("[of_formula] input: " ^ Sexp.to_string phi);
    print @@ lazy ("[of_formula] output: " ^ Formula.str_of ret);
    ret)
  @@
  match phi with
  (* constant *)
  | Sexp.Atom "true" -> Formula.mk_true ()
  | Sexp.Atom "false" -> Formula.mk_false ()
  (* constant variable *)
  | Sexp.Atom name -> (
      match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
      | Some sort ->
          assert (Term.is_bool_sort sort);
          Formula.of_bool_term @@ Term.mk_var (Ident.Tvar name) sort
      | None -> (
          match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
          | Some sort ->
              let sargs, sret = Sort.args_ret_of sort in
              assert (Term.is_bool_sort sret);
              let deps =
                (* only a declare-fun read as an unknown and a
                   declare-dep-exists-fun register dependency arguments; a
                   predicate declared by declare-rel or by a kind declaration
                   (declare-fnp, declare-wfp, declare-uniqp, declare-totp,
                   declare-nep, declare-dwfp, declare-nwfp, declare-parityp,
                   declare-admp, declare-admcp, declare-integp) has none *)
                Option.value ~default:[]
                @@ Map.Poly.find envs.dep_map (Ident.Tvar name)
              in
              Formula.mk_atom
              @@ Atom.mk_pvar_app (Ident.Pvar name) sargs
                   (List.map ~f:(Tuple2.uncurry Term.mk_var) deps)
          | None -> (
              (* no arguments function *)
              match Map.Poly.find envs.fenv (Ident.Tvar name) with
              | Some (fargs, T_bool.SBool, _, true, _)
                when List.length (with_lifted_args envs name fargs [])
                     = List.length fargs ->
                  (* A source-nullary recursive definition may carry captured
                     universals internally. Complete only those arguments;
                     written parameters still require an application. *)
                  let args = with_lifted_args envs name fargs [] in
                  Formula.of_bool_term
                  @@ Term.mk_fvar_app (Ident.Tvar name) (List.map ~f:snd fargs)
                       T_bool.SBool args
              | Some
                  ( [],
                    T_bool.SBool,
                    Term.FunApp (T_bool.Formula phi, [], _),
                    false,
                    _ ) ->
                  if inline then phi
                  else
                    Formula.of_bool_term
                    @@ Term.mk_fvar_app (Ident.Tvar name) [] T_bool.SBool []
              | _ -> refuse_unbound name)))
  (* logical operation *)
  | Sexp.List [ Sexp.Atom "not"; phi ] ->
      mk_neg @@ of_formula ~print ~inline envs phi
  | Sexp.List (Sexp.Atom "and" :: phis) ->
      and_of @@ List.rev_map phis ~f:(of_formula ~print ~inline envs)
  | Sexp.List (Sexp.Atom "or" :: phis) ->
      or_of @@ List.rev_map phis ~f:(of_formula ~print ~inline envs)
  | Sexp.List (Sexp.Atom "xor" :: phi :: phis) ->
      (* [:left-assoc], and folded rather than handed over as a list because the
         helper below is binary only and failed an assertion on three *)
      List.fold phis ~init:(of_formula ~print ~inline envs phi) ~f:(fun acc ->
          of_formula ~print ~inline envs >> fun phi -> xor_of [ acc; phi ])
  | Sexp.List (Sexp.Atom op :: (_ :: _ :: _ :: _ as phis))
    when is_right_assoc op ->
      let phis = List.map phis ~f:(of_formula ~print ~inline envs) in
      let rec right_assoc = function
        | [ phi ] -> phi
        | phi :: phis -> mk_imply phi (right_assoc phis)
        | [] -> assert false (* the pattern above gives at least three *)
      in
      right_assoc phis
  | Sexp.List (Sexp.Atom op :: (_ :: _ :: _ :: _ as ts)) when is_chainable op ->
      (* adjacent pairs, conjoined *)
      let ts = List.map ts ~f:(of_term ~print ~inline envs) in
      and_of
      @@ List.map ~f:(fun (t1, t2) ->
             mk_atom @@ source_pred_sym2 ~print envs op t1 t2)
      @@ List.zip_exn (List.drop_last_exn ts) (List.tl_exn ts)
  | Sexp.List [ Sexp.Atom "=>"; phi1; phi2 ] ->
      let phi1 = of_formula ~print ~inline envs phi1 in
      let phi2 = of_formula ~print ~inline envs phi2 in
      mk_imply phi1 phi2
  (* binder *)
  | Sexp.List [ Sexp.Atom "forall"; Sexp.List params; phi ] ->
      let uni_senv, params, renaming =
        of_params ~is_taken:(is_function_name_bound envs) ~print envs.uni_senv params envs.uni_sort envs.dtenv
      in
      mk_forall (Map.Poly.to_alist params)
      @@ of_binder_body ~print ~inline envs uni_senv renaming phi
  | Sexp.List [ Sexp.Atom "exists"; Sexp.List params; phi ] ->
      let uni_senv, params, renaming =
        of_params ~is_taken:(is_function_name_bound envs) ~print envs.uni_senv params envs.uni_sort envs.dtenv
      in
      mk_exists (Map.Poly.to_alist params)
      @@ of_binder_body ~print ~inline envs uni_senv renaming phi
  | Sexp.List [ Sexp.Atom "random"; Sexp.List params; phi ] ->
      let uni_senv, params, renaming = of_random_params ~print ~inline envs params in
      mk_randoms params
      @@ of_binder_body ~print ~inline envs uni_senv renaming phi
  (* let *)
  | Sexp.List [ Sexp.Atom "let"; Sexp.List bounds; phi ] ->
      let bounds =
        List.map bounds ~f:(function
          | Sexp.List [ Sexp.Atom name; t ] ->
              let def =
                source_numeric_rank ~print envs (of_term ~print ~inline envs t)
              in
              (Ident.Tvar name, Term.sort_of def, def)
          | sexp -> failwith @@ "Invalid param: " ^ Sexp.to_string_hum sexp)
      in
      (* SMT-LIB's [let] is PARALLEL: every right-hand side is evaluated in the
         scope OUTSIDE the let, so one binding cannot see another.  Nesting the
         bindings one inside the next makes them sequential, and a right-hand
         side that mentions a name this same [let] binds then picks up the
         sibling instead of the outer one.  That changes the value, and it makes
         the order of the bindings matter where the standard gives it no
         meaning -- swapping two of them changed the verdict.  So the bound
         names that another right-hand side mentions are renamed apart before
         the nesting is built; the others are left alone, because a fresh name
         drawn here moves the whole search afterwards. *)
      let renaming =
        (* [v] is mentioned by another binding iff it occurs free in the
           right-hand side of a binding whose own name is not [v]; the union of
           those occurrences is computed once, since asking it per name costs
           the square of the number of bindings (thousands in one [let] of a
           translated circuit) *)
        let mentioned =
          Set.Poly.union_list
          @@ List.map bounds ~f:(fun (v', _, def) ->
              Set.remove (Term.tvs_of def) v')
        in
        let mentioned_by_others v = Set.mem mentioned v in
        (* A binder whose name the enclosing scope already holds is renamed for
           the second reason: SMT-LIB lets an inner binding shadow an outer one,
           the occurrence referring to the inner, and inserting it into the
           enclosing scope refused the file outright.  Renaming rather than
           sharing the name keeps the result alpha-converted, which the passes
           downstream that are not capture-avoiding assume. *)
        let shadows_an_outer v =
          Map.Poly.mem envs.uni_senv v || is_function_name_bound envs v
        in
        Map.Poly.of_alist_exn
        @@ List.filter_map bounds ~f:(fun (v, sort, _) ->
            if mentioned_by_others v || shadows_an_outer v then
              Some (v, (fresh_binding_variable envs, sort))
            else None)
      in
      let bound_name v =
        match Map.Poly.find renaming v with Some (v', _) -> v' | None -> v
      in
      let uni_senv =
        List.fold bounds ~init:envs.uni_senv ~f:(fun uni_senv (tvar, sort, _) ->
            Map.Poly.add_exn uni_senv ~key:(bound_name tvar) ~data:sort)
      in
      let envs = { envs with uni_senv } in
      let body =
        of_formula ~print ~inline envs
          (rename_bound_occurrences envs (Map.Poly.map renaming ~f:fst) phi)
      in
      List.rev bounds
      |> List.fold ~init:body ~f:(fun body (var, sort, def) ->
          Formula.mk_let_formula (bound_name var) sort def body)
  (* match *)
  | Sexp.List [ Sexp.Atom "match"; scrut; Sexp.List cases ] ->
      let scrut, bound =
        match_scrutinee ~print envs (source_numeric_rank ~print envs (of_term ~print ~inline envs scrut))
      in
      let dt, cases = match_cases envs scrut cases in
      let bound = match_sort_binding envs scrut bound dt in
      let body =
        Formula.or_of
        @@ List.map cases ~f:(fun (guard, binds, body) ->
            let envs, binds, body = match_case_scope envs binds body in
            let body = of_formula ~print ~inline envs body in
            Formula.and_of
              [
                match_guard dt scrut guard;
                List.fold_right binds ~init:body ~f:(fun (v, sort, def) body ->
                    Formula.mk_let_formula v sort def body);
              ])
      in
      Option.value_map bound ~default:body ~f:(fun (v, sort, def) ->
          Formula.mk_let_formula v sort def body)
  (* ite *)
  | Sexp.List [ Sexp.Atom "ite"; cond; then_; else_ ] ->
      let t =
        T_bool.mk_if_then_else
          (of_term ~print ~inline envs cond)
          (of_term ~print ~inline envs then_)
          (of_term ~print ~inline envs else_)
      in
      if T_bool.is_sbool t then Formula.eq t @@ T_bool.mk_true ()
      else assert false
  (* unary predicate symbol application *)
  | Sexp.List [ Sexp.Atom op; t ] when is_pred_sym1 op ->
      mk_atom @@ of_pred_sym1 op @@ of_term ~print ~inline envs t
  (* binary predicate symbol application *)
  | Sexp.List [ Sexp.Atom op; t1; t2 ] when is_pred_sym2 op ->
      mk_atom
      @@ source_pred_sym2 ~print envs op
           (of_term ~print ~inline envs t1)
           (of_term ~print ~inline envs t2)
  (* predicate symbol application *)
  | Sexp.List (Sexp.Atom "distinct" :: ts) ->
      (* pairwise over the POSITIONS of the operand list.  Collecting the
         operands into a set first drops a repeated one, and [(distinct x x)]
         then became the empty conjunction, i.e. true, where SMT-LIB makes
         [distinct] false as soon as two of its arguments are equal -- including
         two occurrences of the same variable, or two references to one [let]
         binding.  Ground repetitions hid it: two separately parsed literals
         carry different fresh sort variables at this point, so they do not
         collapse, and [(distinct 0 0)] was refuted correctly all along. *)
      let ts = List.map ts ~f:(of_term ~print ~inline envs) in
      let rec pairs = function
        | [] -> []
        | t :: rest ->
            List.map rest ~f:(fun u ->
                let t, u = source_numeric_pair ~print envs "=" t u in
                Formula.neq t u)
            @ pairs rest
      in
      and_of @@ pairs ts
  (* datatype predicate application *)
  | Sexp.List [ Sexp.List [ Sexp.Atom "_"; Sexp.Atom "is"; constructor ]; t ] ->
      mk_atom
      @@ datatype_tester ~print envs constructor (of_term ~print ~inline envs t)
  (* (! t attr ...): every attribute (:named, :pattern, :weight, :qid, ...)
     is dropped *)
  | Sexp.List (Sexp.Atom "!" :: t :: attrs) ->
      print
      @@ lazy
           (sprintf "! attributes dropped: %s"
           @@ String.concat_map_list ~sep:" " attrs ~f:Sexp.to_string);
      of_formula ~print ~inline envs t
  (* [select] over an array of Bool.  SMT-LIB has no separate syntactic class of
     formulas -- a formula *is* a term of sort Bool -- so a select that returns Bool
     may stand wherever a formula is expected, and both z3 and cvc5 accept it there.
     The case below looks an application's head up as a *name*, in the signature and
     then among the bound variables, which an operator is not, so without this arm the
     standard spelling failed with "select is not bound".  The arm below also accepts
     the array variable applied directly, [(p x)], and keeps doing so: that one is *not*
     standard SMT-LIB -- applying a variable is not first-order, and cvc5 rejects it with
     "Expecting function-like symbol" -- but z3 takes it, inputs here are written with it,
     and the two read to the same term.  So both are accepted and [(select p x)] is the
     one to write in a file another tool may read.  A read of a sequence of Bool,
     [(seq.nth s i)], is the same case for the same reason. *)
  | Sexp.List (Sexp.Atom ("select" | "seq.nth") :: _) ->
      Formula.of_bool_term @@ of_term ~print ~inline envs phi
  (* predicate variable application *)
  | Sexp.List (Sexp.Atom name :: args) -> (
      print @@ lazy (sprintf "[formula] predicate %s" name);
      let args = List.map args ~f:(of_term ~print ~inline envs) in
      match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
      | Some sort ->
          let sargs, sret = Sort.args_ret_of sort in
          assert (Term.is_bool_sort sret);
          let deps =
            (* only a declare-fun read as an unknown and a
               declare-dep-exists-fun register dependency arguments; a
               predicate declared by declare-rel or by a kind declaration
               (declare-fnp, declare-wfp, declare-uniqp, declare-totp,
               declare-nep, declare-dwfp, declare-nwfp, declare-parityp,
               declare-admp, declare-admcp, declare-integp) has none *)
            Option.value ~default:[]
            @@ Map.Poly.find envs.dep_map (Ident.Tvar name)
          in
          Formula.mk_atom
          @@ Atom.mk_pvar_app (Ident.Pvar name) sargs
               (List.map ~f:(Tuple2.uncurry Term.mk_var) deps @ args)
      | None -> (
          match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
          | Some sort when T_array.is_sarray sort ->
              (* forall-fun predicate *)
              Formula.of_bool_term
              @@ T_array.mk_select_app (Term.mk_var (Ident.Tvar name) sort) args
          | Some sort ->
              let sargs, sret = Sort.args_ret_of sort in
              assert (Term.is_bool_sort sret);
              Formula.of_bool_term
              @@ Term.mk_fvar_app (Ident.Tvar name) sargs T_bool.SBool args
          | None -> (
              match Map.Poly.find envs.fenv (Tvar name) with
              | Some (fargs, T_bool.SBool, t, false, _) ->
                  if inline then (
                    assert (List.length args = List.length fargs);
                    inline_with_reads_folded
                      ~map_term:(fun phi ~f -> Formula.map_term ~f phi)
                      ~names_of:Formula.names_spelled_in ~subst:Formula.subst
                      (Map.Poly.of_alist_exn
                      @@ List.zip_exn (List.map ~f:fst fargs)
                      @@ List.map2_exn fargs args
                           ~f:(with_formal_sort ~print ~rigid:(rigid_of envs.uni_sort) envs.uni_senv))
                    @@ refresh_binders_formula @@ Formula.of_bool_term t)
                  else
                    Formula.of_bool_term
                    @@ Term.mk_fvar_app (Ident.Tvar name)
                         (List.map ~f:snd fargs) T_bool.SBool args
              | Some (fargs, T_bool.SBool, _, true, _) ->
                  let args = with_lifted_args envs name fargs args in
                  assert (List.length args = List.length fargs);
                  Formula.of_bool_term
                  @@ Term.mk_fvar_app (Tvar name) (List.map ~f:snd fargs)
                       T_bool.SBool args
              | Some _ -> failwith @@ sprintf "%s is ill-defined" name
              | None -> (
                  match DTEnv.look_up_func envs.dtenv name with
                  | Some (_, Datatype.FSel _) ->
                      (* A Boolean selector is a formula as well as a term.
                         Preserve the enclosing term/function bindings above. *)
                      Formula.of_bool_term @@ of_term ~print ~inline envs phi
                  | _ -> refuse_unbound name))))
  | sexp -> failwith @@ "parse error : " ^ Sexp.to_string_hum sexp

and is_included_pvars ~print ~inline envs = function
  | [] -> false
  | Sexp.List [ Sexp.Atom _; t ] :: sexps ->
      let phi = of_formula ~print ~inline envs t in
      if
        LogicOld.Formula.number_of_pvar_apps true phi
        + LogicOld.Formula.number_of_pvar_apps false phi
        > 0
      then true
      else is_included_pvars ~print ~inline envs sexps
  | sexp :: _ -> failwith @@ "invalid bounds: " ^ Sexp.to_string_hum sexp

(* Rename the source before expansion. Free names copied from an earlier
   definition keep their identity, instead of becoming this binder's variables. *)
and of_binder_body ~print ~inline envs uni_senv renaming phi =
  let envs = { envs with uni_senv } in
  of_formula ~print ~inline envs
    (rename_bound_occurrences envs (Map.Poly.map renaming ~f:fst) phi)

and of_term ~print ~inline (envs : Problem.envs) term =
  with_source_numeric_scope ~print envs
    ~constrs_of:(fun term ->
      let _, _, constrs = Typeinf.cgen_term ~print envs.uni_senv term in
      constrs)
    ~subst_sorts:Term.subst_sorts ~map_term:(fun root ~f -> Term.map_term true ~f root)
    (fun () -> of_term_raw ~print ~inline envs term)

and of_term_raw ~print ~inline envs =
  let open Term in
  function
  (* ite *)
  | Sexp.List [ Sexp.Atom "ite"; cond; then_; else_ ] ->
      T_bool.mk_if_then_else
        (of_term ~print ~inline envs cond)
        (of_term ~print ~inline envs then_)
        (of_term ~print ~inline envs else_)
  (* let *)
  | Sexp.List [ Sexp.Atom "let"; Sexp.List def; body ] -> (
      let aux def body =
        let def =
          List.rev_map def ~f:(function
            | Sexp.List [ Sexp.Atom name; t ] ->
                ( Ident.Tvar name,
                  source_numeric_rank ~print envs
                    (of_term ~print ~inline envs t) )
            | sexp -> failwith @@ "invalid param : " ^ Sexp.to_string_hum sexp)
        in
        (* SMT-LIB's [let] is PARALLEL -- see the comment on the formula-position
           [let] above, which this shares: the right-hand sides are evaluated
           outside the binding, so nesting them makes a right-hand side that
           mentions a sibling's name capture it. *)
        let renaming =
          (* computed once, as for the formula-position [let] above *)
          let mentioned =
            Set.Poly.union_list
            @@ List.map def ~f:(fun (v', t) -> Set.remove (Term.tvs_of t) v')
          in
          let mentioned_by_others v = Set.mem mentioned v in
          (* and the second reason, as above: an inner binding may shadow an
             outer one, which used to be refused *)
          let shadows_an_outer v =
            Map.Poly.mem envs.uni_senv v || is_function_name_bound envs v
          in
          Map.Poly.of_alist_exn
          @@ List.filter_map def ~f:(fun (v, t) ->
              if mentioned_by_others v || shadows_an_outer v then
                Some (v, (fresh_binding_variable envs, Term.sort_of t))
              else None)
        in
        let bound_name v =
          match Map.Poly.find renaming v with Some (v', _) -> v' | None -> v
        in
        let uni_senv =
          List.fold def ~init:envs.uni_senv ~f:(fun uni_senv (tvar, t) ->
              Map.Poly.add_exn uni_senv ~key:(bound_name tvar)
                ~data:(Term.sort_of t))
        in
        let envs = { envs with uni_senv } in
        let body =
          of_term ~print ~inline envs
            (rename_bound_occurrences envs (Map.Poly.map renaming ~f:fst) body)
        in
        List.fold def ~init:body ~f:(fun acc (tvar, t) ->
            Term.mk_let_term (bound_name tvar) (Term.sort_of t) t acc)
      in
      try
        if is_included_pvars ~print ~inline envs def then
          failwith
            "Invalid let-expressions (It is not allowed to use let-term \
             binding predicate applications into some name.)"
        else aux def body
      with exn_ when not (Common.Timer.is_async exn_) -> aux def body)
  (* match: the cases as an [ite] chain on the testers; the last reachable
     case needs no test, since the cases are exhaustive *)
  | Sexp.List [ Sexp.Atom "match"; scrut; Sexp.List cases ] ->
      let scrut, bound =
        match_scrutinee ~print envs (source_numeric_rank ~print envs (of_term ~print ~inline envs scrut))
      in
      let dt, cases = match_cases envs scrut cases in
      let bound = match_sort_binding envs scrut bound dt in
      let rec chain = function
        | [] -> assert false (* [match_cases] refuses an empty match *)
        | (guard, binds, body) :: rest ->
            let envs, binds, body = match_case_scope envs binds body in
            let body =
              List.fold_right binds ~init:(of_term ~print ~inline envs body)
                ~f:(fun (v, sort, def) body -> Term.mk_let_term v sort def body)
            in
            if List.is_empty rest then body
            else
              T_bool.mk_if_then_else
                (T_bool.of_formula (match_guard dt scrut guard))
                body (chain rest)
      in
      let body = chain cases in
      Option.value_map bound ~default:body ~f:(fun (v, sort, def) ->
          Term.mk_let_term v sort def body)
  (* lambda (a Z3 extension, not SMT-LIB: it denotes an array value) *)
  | Sexp.List [ Sexp.Atom "lambda"; Sexp.List params; body ] -> (
      match params with
      | [ param ] ->
          let x, si = bind_of_sexp ~print envs.uni_sort envs.dtenv param in
          (* Bind the source before expansion, so free names copied from an
             older definition cannot become lambda-bound. Also avoid every
             source name before parsing, including names not yet looked up. *)
          let rec source_names = function
            | Sexp.Atom name -> Set.Poly.singleton (Ident.Tvar name)
            | Sexp.List terms ->
                Set.Poly.union_list (List.map terms ~f:source_names)
          in
          let taken = source_names body in
          let rec draw () =
            let v =
              Ident.mk_fresh_tvar ~prefix:(Some (Ident.name_of_tvar x)) ()
            in
            if Set.mem taken v || Map.Poly.mem envs.uni_senv v
               || is_function_name_bound envs v then draw ()
            else v
          in
          let x' = draw () in
          let uni_senv = Map.Poly.set envs.uni_senv ~key:x' ~data:si in
          let body =
            of_term ~print ~inline { envs with uni_senv }
              (rename_bound_occurrences { envs with uni_senv }
                 (Map.Poly.singleton x x') body)
          in
          T_array.mk_lambda (x', si) (Term.sort_of body) body
      | _ ->
          (* a multi-parameter lambda denotes a non-binary Z3 array, which
             [T_array.SArray] cannot represent *)
          failwith
          @@ sprintf
               "[lambda] only single-parameter lambdas are supported, but got \
                %d parameters"
          @@ List.length params)
  (* constant *)
  | Sexp.Atom op when is_con op -> of_con op
  (* A symbol in scope denotes its binding, before any reading of its spelling
     as a literal.  [+2], [.5], [inf] and [nan] are symbols (a declared [+2] is
     not the number 2), while a NUMERAL or DECIMAL starts with a digit and a
     negative one with [-] and a digit ([is_negative_numeral_spelling]), and
     those are never symbols, so they skip the lookup; a binder of a negative
     numeral spelling, which no declaration can introduce, is refused when the
     body uses it. *)
  | Sexp.Atom name
    when (not (String.is_empty name))
         && (not (Char.is_digit name.[0]))
         && is_term_symbol_bound envs name -> (
      if is_negative_numeral_spelling name then
        refuse_numeral_symbol ~what:"binder" name;
      match bound_symbol_term ~inline envs name with
      | Some t -> t
      | None -> assert false (* [is_term_symbol_bound] *))
  (* constant variable *)
  | Sexp.Atom name -> (
      if
        String.is_prefix name ~prefix:"\"" && String.is_suffix name ~suffix:"\""
      then
        (* Between the delimiters, SMT-LIB's one escape is a DOUBLED quotation
           mark standing for a single one; there is no backslash escape for it.
           Stripping the delimiters and stopping there left both quotes in the
           value, so [""""] and ["\\u{22}"] -- two spellings of the same
           one-character string -- compared unequal.  Only that one substitution
           is made: a general unescape would also change the backslashes the
           value is entitled to contain, and the [\\u{...}] form is decoded
           further down the line rather than here. *)
        T_string.make
        @@ String.substr_replace_all ~pattern:"\"\"" ~with_:"\""
        @@ String.sub name ~pos:1 ~len:(String.length name - 2)
      else
        try
          if String.length name < 3 || not (String.is_prefix name ~prefix:"#x")
          then invalid_arg "Not a valid #x... bitvector literal";
          let hex_part = String.slice name 2 (String.length name) in
          let bitwidth = String.length hex_part * 4 in
          T_bv.mk_bvnum ~size:(Some bitwidth) (Z.of_string ("0x" ^ hex_part))
        with exn_ when not (Common.Timer.is_async exn_) -> (
          try
            if
              String.length name < 3 || not (String.is_prefix name ~prefix:"#o")
            then invalid_arg "Not a valid #o... bitvector literal";
            let oct_part = String.slice name 2 (String.length name) in
            let bitwidth = String.length oct_part * 3 in
            T_bv.mk_bvnum ~size:(Some bitwidth) (Z.of_string ("0o" ^ oct_part))
          with exn_ when not (Common.Timer.is_async exn_) -> (
            try
              if
                String.length name < 3
                || not (String.is_prefix name ~prefix:"#b")
              then invalid_arg "Not a valid #b... bitvector literal";
              let bin_part = String.slice name 2 (String.length name) in
              let bitwidth = String.length bin_part in
              T_bv.mk_bvnum ~size:(Some bitwidth)
                (Z.of_string ("0b" ^ bin_part))
            with exn_ when not (Common.Timer.is_async exn_) -> (
              try
                (* [T_num.mk_value] also reads [inf], [nan], [infinity],
                   [+2] and [.5], which are symbols here and never numbers:
                   only an atom spelled as a numeral or decimal, or as a
                   negative one, is a literal; an undeclared [+2] is unbound,
                   as z3 and cvc5 report it *)
                if
                  String.is_empty name
                  || not
                       (Char.is_digit name.[0]
                       || is_negative_numeral_spelling name)
                then invalid_arg "Not a numeral";
                let numeral = T_num.mk_value name in
                (* DECIMAL has Real rank even when its value is integral.
                   Preserve that source rank before any defaulting, or the
                   Int default truncates 1.5 and reverses verdicts. *)
                if String.contains name '.' then
                  match numeral with
                  | FunApp (T_num.Value (value, _), [], _) ->
                      T_real.mk_real (Q.of_string value)
                  | _ -> assert false
                else numeral
              with exn_ when not (Common.Timer.is_async exn_) -> (
                (* other cases *)
                match bound_symbol_term ~inline envs name with
                | Some t -> t
                | None -> (
                    match DTEnv.look_up_func envs.dtenv name with
                    | Some (dt, Datatype.FCons cons)
                      when List.is_empty @@ Datatype.sels_of_cons cons ->
                        (* fresh sort parameters per occurrence, as
                           [sort_of_sexp] does: two instantiations of a
                           parametric datatype in one file used to share the
                           parameters and fail type inference *)
                        T_dt.mk_cons (Datatype.fresh_of dt) name []
                    | _ -> refuse_unbound name)))))
      )
  (* unary function symbol application *)
  | Sexp.List [ Sexp.Atom op; t ] when is_fun_sym1 op ->
      of_fun_sym1 op @@ of_term ~print ~inline envs t
  (* binary function symbol application *)
  | Sexp.List [ Sexp.Atom op; t1; t2 ] when is_fun_sym2 op ->
      source_fun_sym2 ~print envs op
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  (* an operator with a first argument of its own, applied to more than two *)
  | Sexp.List (Sexp.Atom op :: t1 :: t2 :: (_ :: _ as ts))
    when is_left_assoc2 op ->
      List.fold (t2 :: ts) ~init:(of_term ~print ~inline envs t1) ~f:(fun acc ->
          of_term ~print ~inline envs >> source_fun_sym2 ~print envs op acc)
  (* function symbol application *)
  | Sexp.List (Sexp.Atom op :: arg :: args) when allow_mult_args op ->
      List.fold args ~init:(of_term ~print ~inline envs arg) ~f:(fun acc ->
          of_term ~print ~inline envs >> source_fun_sym2 ~print envs op acc)
  (* datatype function application *)
  | Sexp.List (Sexp.Atom name :: args) as t
    when DTEnv.name_is_func envs.dtenv name -> (
      print @@ lazy (sprintf "[term] datatype func %s" name);
      match
        ( DTEnv.look_up_func envs.dtenv name,
          List.map args ~f:(of_term ~print ~inline envs) )
      with
      | Some (dt, Datatype.FCons _), args ->
          T_dt.mk_cons (Datatype.fresh_of dt) name args
          (* fresh sort parameters per occurrence, see above *)
      | Some (dt, Datatype.FSel _), [ arg ] ->
          T_dt.mk_sel (Datatype.fresh_of dt) name arg
      | Some (_, Datatype.FSel _), _ -> failwith ""
      | _ -> T_bool.of_formula @@ of_formula ~print ~inline envs t)
  (* array function application *)
  | Sexp.List [ Sexp.Atom "select"; t1; t2 ] -> (
      let arr = of_term ~print ~inline envs t1 in
      let i = of_term ~print ~inline envs t2 in
      match sort_of arr with
      | T_array.SArray (s1, s2) -> T_array.mk_select s1 s2 arr i
      | _ -> failwith "")
  | Sexp.List [ Sexp.Atom "store"; t1; t2; t3 ] -> (
      let arr = of_term ~print ~inline envs t1 in
      let i = of_term ~print ~inline envs t2 in
      let e = of_term ~print ~inline envs t3 in
      match sort_of arr with
      | T_array.SArray (s1, s2) -> T_array.mk_store s1 s2 arr i e
      | _ -> failwith "")
  (* sequence function application: SMT-LIB's parametric [(Seq s)], which Z3's
     sequence solver decides.  The element sort is read off the argument rather
     than declared, as it is for [select] and [store] above. *)
  | Sexp.List [ Sexp.Atom "seq.unit"; t1 ] ->
      let e = of_term ~print ~inline envs t1 in
      T_seq.mk_unit (sort_of e) e
  | Sexp.List [ Sexp.Atom "seq.len"; t1 ] -> (
      let sq = of_term ~print ~inline envs t1 in
      match sort_of sq with
      | T_seq.SSeq se -> T_seq.mk_len se sq
      | s ->
          failwith
          @@ sprintf "[seq.len] not a sequence: %s" (Term.str_of_sort s))
  | Sexp.List [ Sexp.Atom "seq.nth"; t1; t2 ] -> (
      let sq = of_term ~print ~inline envs t1 in
      let i = of_term ~print ~inline envs t2 in
      match sort_of sq with
      | T_seq.SSeq se -> T_seq.mk_nth se sq i
      | s ->
          failwith
          @@ sprintf "[seq.nth] not a sequence: %s" (Term.str_of_sort s))
  | Sexp.List [ Sexp.Atom "seq.store"; t1; t2; t3 ] -> (
      (* not an SMT-LIB symbol: SMT-LIB sequences have no write.  A front end
         that models one otherwise has to spell out the three-piece
         concatenation at every write, which makes it several nodes and takes
         the frame property out of the syntax. *)
      let sq = of_term ~print ~inline envs t1 in
      let i = of_term ~print ~inline envs t2 in
      let e = of_term ~print ~inline envs t3 in
      match sort_of sq with
      | T_seq.SSeq se -> T_seq.mk_store se sq i e
      | s ->
          failwith
          @@ sprintf "[seq.store] not a sequence: %s" (Term.str_of_sort s))
  | Sexp.List [ Sexp.Atom "seq.extract"; t1; t2; t3 ] -> (
      let sq = of_term ~print ~inline envs t1 in
      let off = of_term ~print ~inline envs t2 in
      let len = of_term ~print ~inline envs t3 in
      match sort_of sq with
      | T_seq.SSeq se -> T_seq.mk_extract se sq off len
      | s ->
          failwith
          @@ sprintf "[seq.extract] not a sequence: %s" (Term.str_of_sort s))
  | Sexp.List (Sexp.Atom "seq.++" :: t1 :: ts) when not (List.is_empty ts) -> (
      (* n-ary in SMT-LIB, left-associated here *)
      let sq = of_term ~print ~inline envs t1 in
      match sort_of sq with
      | T_seq.SSeq se ->
          List.fold ts ~init:sq ~f:(fun acc t ->
              T_seq.mk_concat se acc (of_term ~print ~inline envs t))
      | s ->
          failwith @@ sprintf "[seq.++] not a sequence: %s" (Term.str_of_sort s)
      )
  | Sexp.List [ Sexp.Atom "as"; Sexp.Atom "seq.empty"; sort ]
  | Sexp.List [ Sexp.List [ Sexp.Atom "as"; Sexp.Atom "seq.empty"; sort ] ] -> (
      match sort_of_sexp ~print envs.uni_sort envs.dtenv None sort with
      | T_seq.SSeq se -> T_seq.mk_empty se
      | s ->
          failwith
          @@ sprintf "[seq.empty] not a sequence sort: %s" (Term.str_of_sort s))
  | Sexp.List (Sexp.Atom "!" :: t :: _attrs) -> of_term ~print ~inline envs t
  (* indexed bit-vector literal (_ bvN w) *)
  | Sexp.List [ Sexp.Atom "_"; Sexp.Atom bv; Sexp.Atom width ]
    when String.length bv > 2
         && String.is_prefix bv ~prefix:"bv"
         && String.for_all (String.drop_prefix bv 2) ~f:Char.is_digit ->
      T_bv.mk_bvnum
        ~size:(Some (index_numeral ~what:"(_ bvN w)" width))
        (Z.of_string (String.drop_prefix bv 2))
  | Sexp.List [ Sexp.List [ Sexp.Atom "as"; Sexp.Atom "const"; sort ]; value ]
    -> (
      let arr_sort = sort_of_sexp ~print envs.uni_sort envs.dtenv None sort in
      let arr_value = of_term ~print ~inline envs value in
      match arr_sort with
      | T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 arr_value
      | _ -> failwith "")
  (* Keep theory-specific qualified identifiers above this constructor path. *)
  | Sexp.List [ Sexp.Atom "as"; Sexp.Atom name; sort ] ->
      qualified_identifier ~print
        ~term_of_sexp:(of_term ~print ~inline envs)
        envs name sort []
  | Sexp.List
      (Sexp.List [ Sexp.Atom "as"; Sexp.Atom name; sort ] :: (_ :: _ as args))
    ->
      qualified_identifier ~print
        ~term_of_sexp:(of_term ~print ~inline envs)
        envs name sort args
  (* bitvector function application *)
  (* [int2bv] is z3's and cvc5's older name for [int_to_bv]: both take the
     integer modulo 2^n *)
  | Sexp.List
      [
        Sexp.List
          [ Sexp.Atom "_"; Sexp.Atom ("int_to_bv" | "int2bv"); Sexp.Atom bits ];
        t1;
      ] ->
      let t1 = of_term ~print ~inline envs t1 in
      T_irb.mk_int_to_bv
        ~size:(Some (index_numeral ~what:"(_ int_to_bv n)" bits))
        t1
  | Sexp.List
      [
        Sexp.List
          [ Sexp.Atom "_"; Sexp.Atom "extract"; Sexp.Atom h; Sexp.Atom l ];
        t1;
      ] ->
      let t1 = of_term ~print ~inline envs t1 in
      T_bv.mk_bvextract ~size:None
        (index_numeral ~what:"(_ extract h l)" h)
        (index_numeral ~what:"(_ extract h l)" l)
        t1
  | Sexp.List
      [
        Sexp.List [ Sexp.Atom "_"; Sexp.Atom "sign_extend"; Sexp.Atom ext ]; t1;
      ] ->
      let t1 = of_term ~print ~inline envs t1 in
      let size = match Term.sort_of t1 with T_bv.SBV s -> s | _ -> None in
      T_bv.mk_bvsext ~size (index_numeral ~what:"(_ sign_extend n)" ext) t1
  | Sexp.List
      [
        Sexp.List [ Sexp.Atom "_"; Sexp.Atom "zero_extend"; Sexp.Atom ext ]; t1;
      ] ->
      let t1 = of_term ~print ~inline envs t1 in
      let size = match Term.sort_of t1 with T_bv.SBV s -> s | _ -> None in
      T_bv.mk_bvzext ~size (index_numeral ~what:"(_ zero_extend n)" ext) t1
  (* [repeat], [rotate_left] and [rotate_right] are declared by the QF_BV logic
     rather than the theory, which defines them by [concat] and [extract]:
     [(repeat 1 t)] is [t] and [(repeat i+1 t)] is [(concat t (repeat i t))];
     rotating an [n]-bit [t] left by [i] is rotating it by [i mod n], and by
     [k] in [1, n-1] is [(concat (extract n-1-k 0 t) (extract n-1 n-k t))];
     rotating right by [k] is rotating left by [n - k].  The width [n] is the
     operand's, so it must be known here; every bit-vector term this reader
     builds from a declared symbol or a literal carries it.  Without these arms
     the application fell through to the catch-all and was an uncaught parse
     error. *)
  | Sexp.List
      [ Sexp.List [ Sexp.Atom "_"; Sexp.Atom "repeat"; Sexp.Atom i ]; t1 ] -> (
      let t1 = of_term ~print ~inline envs t1 in
      match (index_numeral ~what:"(_ repeat i)" i, Term.sort_of t1) with
      | i, _ when i < 1 ->
          failwith "(_ repeat i) needs i >= 1 (the QF_BV logic declaration)"
      | i, T_bv.SBV (Some n) ->
          List.fold (List.init (i - 1) ~f:Fn.id) ~init:(t1, n)
            ~f:(fun (acc, size) _ ->
              ( T_bv.mk_bvconcat ~size1:(Some n) ~size2:(Some size) t1 acc,
                size + n ))
          |> fst
      | _ ->
          failwith
            "(_ repeat i) is supported only on an operand whose width is known \
             where it is read")
  | Sexp.List
      [
        Sexp.List
          [
            Sexp.Atom "_";
            Sexp.Atom (("rotate_left" | "rotate_right") as dir);
            Sexp.Atom i;
          ];
        t1;
      ] -> (
      let t1 = of_term ~print ~inline envs t1 in
      let i = index_numeral ~what:(sprintf "(_ %s i)" dir) i in
      match Term.sort_of t1 with
      | T_bv.SBV (Some n) ->
          let k = i % n in
          let k = if String.equal dir "rotate_left" then k else (n - k) % n in
          if k = 0 then t1
          else
            let size = Some n in
            T_bv.mk_bvconcat ~size1:(Some (n - k)) ~size2:(Some k)
              (T_bv.mk_bvextract ~size (n - 1 - k) 0 t1)
              (T_bv.mk_bvextract ~size (n - 1) (n - k) t1)
      | _ ->
          failwith
            (sprintf
               "(_ %s i) is supported only on an operand whose width is known \
                where it is read"
               dir))
  (* an [(_ bvN w)] arm stood here too, from the branch this was merged from.
     The one above subsumes it and additionally checks that what follows "bv"
     is a numeral, so `(_ bvfoo 8)` is not read as a literal; this one could
     never be reached. *)
  (* function variable application *)
  | Sexp.List (Sexp.Atom name :: args)
    when match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
         | Some sort -> T_array.is_sarray sort
         | None -> false ->
      (* a forall-fun with a non-Bool result applied to arguments *)
      let sort = Map.Poly.find_exn envs.uni_senv (Ident.Tvar name) in
      T_array.mk_select_app
        (Term.mk_var (Ident.Tvar name) sort)
        (List.map args ~f:(of_term ~print ~inline envs))
  | Sexp.List (Sexp.Atom name :: args) as t -> (
      match Map.Poly.find envs.fenv (Tvar name) with
      | Some (fargs, sret, term, false, _) ->
          if inline then
            let sub =
              Map.Poly.of_alist_exn
              @@ List.zip_exn (List.map ~f:fst fargs)
              @@ List.map2_exn fargs
                   (List.map args ~f:(of_term ~print ~inline envs))
                   ~f:(with_formal_sort ~print ~rigid:(rigid_of envs.uni_sort) envs.uni_senv)
            in
            inline_with_reads_folded
              ~map_term:(fun t ~f -> Term.map_term true ~f t)
              ~names_of:(fun t -> Formula.names_spelled_in (Formula.eq t t))
              ~subst:Term.subst sub
            @@ refresh_binders_term term
          else
            Term.mk_fvar_app (Ident.Tvar name) (List.map ~f:snd fargs) sret
            @@ List.map args ~f:(of_term ~print ~inline envs)
      | Some (fargs, sret, _, true, _) ->
          Term.mk_fvar_app (Ident.Tvar name) (List.map ~f:snd fargs) sret
          @@ with_lifted_args envs name fargs
          @@ List.map args ~f:(of_term ~print ~inline envs)
      | _ -> (
          match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
          | Some sort ->
              let sargs, sret = Sort.args_ret_of sort in
              if Term.is_bool_sort sret then
                T_bool.of_formula @@ of_formula ~print ~inline envs t
              else (
                assert (List.length args = List.length sargs);
                Term.mk_fvar_app (Ident.Tvar name) sargs sret
                @@ List.map args ~f:(of_term ~print ~inline envs))
          | None -> T_bool.of_formula @@ of_formula ~print ~inline envs t))
  | t -> T_bool.of_formula @@ of_formula ~print ~inline envs t

and dist_of_sexp ~print ~inline envs = function
  | Sexp.List [ Sexp.Atom "Uniform"; t1; t2 ] ->
      Rand.mk_uniform
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  | Sexp.List [ Sexp.Atom "Gauss"; t1; t2 ] ->
      Rand.mk_gauss
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  | Sexp.List [ Sexp.Atom "IntUniform"; t1; t2 ] ->
      Rand.mk_int_uniform
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  | _ -> assert false

and of_random_params ~print ~inline envs sexp =
  (* Distributions have parallel outer scope. Parse each once before extending
     the environment, and never rename their copied outer references. Only the
     source body is renamed before definition expansion. *)
  let params = List.map sexp ~f:(function
    | Sexp.List [ Sexp.Atom name; dist ] ->
        (Ident.Tvar name, dist_of_sexp ~print ~inline envs dist)
    | sexp -> failwith @@ "error of " ^ Sexp.to_string sexp)
  in
  let typed_params = List.map params ~f:(fun (name, rand) ->
      let sort = match Rand.sort_of rand with
        | T_real.SReal -> "Real"
        | T_int.SInt -> "Int"
        | _ -> assert false
      in
      Sexp.List [Sexp.Atom (Ident.name_of_tvar name); Sexp.Atom sort])
  in
  let uni_senv, _, renaming =
    of_params ~is_taken:(is_function_name_bound envs) ~print envs.uni_senv
      typed_params envs.uni_sort envs.dtenv
  in
  (uni_senv,
   List.map params ~f:(fun (name, rand) ->
       (Option.value_map (Map.Poly.find renaming name) ~default:name ~f:fst, rand)),
   renaming)

(*let restrict_head bounds args fml =
  List.fold args ~init:(bounds, [], fml)
    ~f:(fun (bounds, args, fml) arg ->
        let arg_sort : Sort.t = Term.sort_of arg in
        let new_name : Ident.tvar = Ident.mk_fresh_head_arg () in
        let new_arg : Term.t = Term.mk_var new_name arg_sort in
        (new_name, arg_sort) :: bounds, new_arg :: args,
        Formula.and_of [fml; Formula.eq new_arg arg])*)

(* Rename shadowing formals before reading the source body. Free names in an
   expanded older definition belong to its definition site. Validate duplicates
   before drawing names, and leave non-shadowing formals unchanged. *)
let rec definition_scope (envs : Problem.envs) name fargs body =
  let fargs, envs, body, _ = definition_scope_with envs name fargs body [] in
  (fargs, envs, body)

(* [definition_scope] that applies the same renaming of shadowing formals to
   [extras], further expressions over the formals (a declared measure). *)
and definition_scope_with (envs : Problem.envs) name fargs body extras =
  ignore (Map.Poly.of_alist_exn fargs);
  let renaming =
    Map.Poly.of_alist_exn
    @@ List.filter_map fargs ~f:(fun (v, _) ->
        if
          Map.Poly.mem envs.uni_senv v
          || is_function_name_bound envs v
          || Stdlib.(v = Ident.Tvar name)
        then Some (v, fresh_binding_variable envs)
        else None)
  in
  let fargs =
    List.map fargs ~f:(fun (v, sort) ->
        (Option.value (Map.Poly.find renaming v) ~default:v, sort))
  in
  let uni_senv =
    List.fold fargs ~init:envs.uni_senv ~f:(fun env (v, sort) ->
        Map.Poly.add_exn env ~key:v ~data:sort)
  in
  ( fargs,
    { envs with uni_senv },
    rename_bound_occurrences { envs with uni_senv } renaming body,
    List.map extras ~f:(rename_bound_occurrences { envs with uni_senv } renaming) )

(* A recursive definition's body may carry the attribute [:decreases m] in an
   annotation [(! body ... :decreases m ...)], the standard syntax for a term
   attribute, which other solvers read and ignore.  Returns the body with that
   attribute removed (the annotation dropped when nothing else remains) and
   [m].  Only the outermost annotation of the body is read. *)
let split_decreases body =
  match body with
  | Sexp.List (Sexp.Atom "!" :: term :: attributes) ->
      let rec split kept = function
        | Sexp.Atom ":decreases" :: measure :: rest ->
            let rest, _ = split [] rest in
            (List.rev_append kept rest, Some measure)
        | attr :: rest -> split (attr :: kept) rest
        | [] -> (List.rev kept, None)
      in
      let attributes, measure = split [] attributes in
      let body =
        if List.is_empty attributes then term
        else Sexp.List (Sexp.Atom "!" :: term :: attributes)
      in
      (body, measure)
  | _ -> (body, None)

(* The declared measure of a recursive definition, read at [Int] over the
   (renamed) formals, and registered under the function's name; nothing is
   registered when the body declares none. *)
let register_measure ~read name = function
  | None -> ()
  | Some measure -> add_declared_measure (Ident.Tvar name) (read measure)

(* A function definition promises its declared result sort even if no later
   assertion calls it. Infer the body against that sort before storing it or
   handing a recursive definition to the solver. Retain rigid quantified sorts. *)
let definition_body ~print ~inline (envs : Problem.envs) sort body =
  let body =
    with_source_numeric_scope ~print envs
      ~constrs_of:(fun term ->
        let _, inferred, constrs =
          Typeinf.cgen_term ~print envs.uni_senv term
        in
        Set.add constrs (Typeinf.CEq (inferred, sort)))
      ~subst_sorts:Term.subst_sorts ~map_term:(fun root ~f -> Term.map_term true ~f root)
      (fun () ->
        if Term.is_bool_sort sort then
          T_bool.of_formula @@ of_formula ~print ~inline envs body
        else of_term ~print ~inline envs body)
  in
  (* Generic numerals otherwise allow a fractional value to be instantiated
     at Int, where substitution truncates it. Preserve its exact Real value
     when imposing the declared result. Integral numerals remain generic. *)
  let literal_constraints = ref Set.Poly.empty in
  Term.iter_term body ~f:(function
    | Term.FunApp (T_num.Value (value, svar), [], _)
      when not (Z.equal (Q.den (Q.of_string value)) Z.one) ->
        literal_constraints :=
          Set.add !literal_constraints
            (Typeinf.CEq (Sort.SVar svar, T_real.SReal))
    | _ -> ());
  Typeinf.typeinf_term ~print ~default:None ~to_sus:true
    ~rigid:(rigid_of envs.uni_sort) ~sort_opt:(Some sort)
    ~constrs_opt:(Some !literal_constraints) body


(* What a [set-logic] name decides here.  [Synthesize] for the Horn and SyGuS
   names (a declared symbol is an unknown to solve for), [Any] for [ALL] and
   [ALL_SUPPORTED] (no theory restriction; the caller's reading stands),
   [Interpreted] for every other accepted name (a declared symbol is
   uninterpreted, to be interpreted by a model), and [Refused reason] for a
   name this reader cannot read, with the reason. *)
type logic_reading =
  | Synthesize
  | Any
  | Interpreted
  | Refused of string

(* Whether [name] is spelled as an SMT-LIB logic, by the naming convention of
   the SMT-LIB logics page: an optional [QF_], then the letter groups in this
   order -- [A] or [AX] (ArraysEx), [UF] (free sort and function symbols), [BV]
   (FixedSizeBitVectors), [FP] (FloatingPoint), [DT] (datatypes), [S]
   (strings), then at most one arithmetic: [IDL], [RDL], [EIA], or [L] / [N]
   before [IA], [RA] or [IRA] -- with at least one group.  The page formally
   defines only some of these names (UFLIA, QF_SLIA, ANIA are not among them),
   but the benchmark library and both z3 and cvc5 use the rest by the same
   convention, so recognising the grammar rather than a list reads every one of
   them.  Returns the letter groups found, or [None] for a name the convention
   does not produce. *)
let smtlib_logic_groups name =
  let n = String.length name in
  let rest_from i = String.sub name ~pos:i ~len:(n - i) in
  let starts i p = String.is_prefix (rest_from i) ~prefix:p in
  let i = if starts 0 "QF_" then 3 else 0 in
  let take i groups opts =
    match List.find opts ~f:(starts i) with
    | Some p -> (i + String.length p, p :: groups)
    | None -> (i, groups)
  in
  let i, gs = take i [] [ "AX"; "A" ] in
  let i, gs = take i gs [ "UF" ] in
  let i, gs = take i gs [ "BV" ] in
  let i, gs = take i gs [ "FP" ] in
  let i, gs = take i gs [ "DT" ] in
  let i, gs = take i gs [ "S" ] in
  let i, gs =
    take i gs
      [ "IDL"; "RDL"; "EIA"; "LIRA"; "NIRA"; "LIA"; "NIA"; "LRA"; "NRA" ]
  in
  if i = n && not (List.is_empty gs) then Some (List.rev gs) else None

let logic_reading = function
  | "HORN" | "QHORN" | "DQHORN" | "SYGUS" -> Synthesize
  | "ALL" | "ALL_SUPPORTED" -> Any
  (* Pure propositional logic, not an SMT-LIB name but one some inputs use. *)
  | "SAT" -> Interpreted
  | name -> (
      match smtlib_logic_groups name with
      | Some groups when List.mem groups "FP" ~equal:String.equal ->
          Refused
            "it includes the floating-point theory (FP), which this reader \
             does not implement"
      | Some _ -> Interpreted
      | None ->
          Refused
            "it is not an SMT-LIB logic name (nor HORN, QHORN, DQHORN, \
             SYGUS, ALL, ALL_SUPPORTED or SAT)")

let mk_dt_sel ?(implicit_params = false) ~print uni_sort dtenv params dt dts =
  let recursive name target args =
    let ret_name = Datatype.name_of_dt target in
    let expected = List.length (Datatype.params_of_dt target) in
    if List.length args <> expected then
      failwith
      @@ sprintf
           "[mk_dt_sel] sort constructor %s expects %d sort argument(s), got %d"
           ret_name expected (List.length args);
    (* A self reference in the native group denotes the current instance.
       Substituting the owner's parameters for different written arguments
       would change the selector's range (next : Tree(T) -> Tree(Bool) read
       as Tree(T) -> Tree(T)). Non-uniform recursion needs
       a representation of distinct recursive instances, not a local index. *)
    if
      String.equal (Datatype.name_of_dt dt) ret_name
      && not Stdlib.(args = Datatype.params_of_dt dt)
    then
      failwith
      @@ sprintf
           "[mk_dt_sel] unsupported non-uniform recursive datatype instance: %s"
           ret_name;
    Datatype.mk_insel name ret_name args
  in
  function
  | Sexp.List [ Sexp.Atom name; (Sexp.Atom ret_name as ret) ]
    when is_local_sort_parameter params ret_name ->
      Datatype.mk_sel name @@ sort_of_sexp ~print uni_sort dtenv params ret
  | Sexp.List [ Sexp.Atom name; (Sexp.List (Sexp.Atom ret_name :: _) as ret) ]
    when is_local_sort_parameter params ret_name ->
      (* A bound parameter has arity zero, even if a same-spelled group member
         takes arguments. Use the ordinary scoped reader to reject it rather
         than read the parameter as a recursive member type. *)
      Datatype.mk_sel name @@ sort_of_sexp ~print uni_sort dtenv params ret
  | Sexp.List [ Sexp.Atom name; (Sexp.Atom ret_name as ret) ] -> (
      match List.find dts ~f:(Datatype.name_of_dt >> String.( = ) ret_name) with
      | Some target ->
          (* Only the legacy shared-parameter declaration syntax supplies
             implicit arguments for a bare recursive member. *)
          recursive name target
            (if implicit_params then Datatype.params_of_dt dt else [])
      | None ->
          Datatype.mk_sel name @@ sort_of_sexp ~print uni_sort dtenv params ret)
  | Sexp.List
      [ Sexp.Atom name; (Sexp.List (Sexp.Atom ret_name :: args) as ret) ] -> (
      match List.find dts ~f:(Datatype.name_of_dt >> String.( = ) ret_name) with
      | Some target ->
          recursive name target
            (List.map args ~f:(sort_of_sexp ~print uni_sort dtenv params))
      | None ->
          Datatype.mk_sel name @@ sort_of_sexp ~print uni_sort dtenv params ret)
  | sexp -> failwith @@ Sexp.to_string sexp

let mk_dt_cons ?(implicit_params = false) ~print uni_sort dtenv params dt dts =
  function
  | Sexp.Atom name | Sexp.List [ Sexp.Atom name ] -> Datatype.mk_cons name
  | Sexp.List (Sexp.Atom name :: sels) ->
      Datatype.mk_cons name
        ~sels:
          (List.map sels
             ~f:(mk_dt_sel ~implicit_params ~print uni_sort dtenv params dt dts))
  | sexp -> failwith @@ sprintf "[mk_dt_cons] %s" (Sexp.to_string sexp)

(* Split a declared datatype group into the groups it really is, in dependency
   order.

   SMT-LIB lets one [declare-datatypes] declare several sorts together, and they
   are all in scope in every body -- so a selector of one member may have any
   sort built over another.  The reader can resolve a sibling only where the
   sibling IS the selector's sort, by naming it; a sort that merely CONTAINS one
   ([(Array Int P)]) has nowhere to put the name and the whole file was refused.
   The obvious repairs do not work, and each fails for a reason worth keeping:
   holding the sibling by value closes a cycle, because a group is represented
   with every member carrying the whole group, and the run then does not
   terminate while expanding it; holding it by name and resolving at the solver
   boundary needs a forward reference the solver's API expresses only for a
   field whose sort IS the recursive sort, not one built over it.

   But a group written together is not always a group: the members declared
   together often do not refer to each other at all, and the case above is
   exactly one of those -- the vector's element type does not mention the
   wrapper that contains it.  So the declared group is split into its strongly
   connected components under "mentions", ordered so that a component comes
   after everything it mentions, and each is declared separately.  A component
   then finds its dependencies already in the environment, by the ordinary
   route, and nothing has to be deferred.  A genuinely mutually recursive group
   stays one component and is declared exactly as before.

   The relation is read off the s-expressions, not the sorts, because the sorts
   are what this is computing. *)
let split_datatype_group names bodies =
  let mentions body =
    let bound, conses =
      match body with
      | Sexp.List [ Sexp.Atom "par"; Sexp.List params; Sexp.List conses ]
      | Sexp.List (Sexp.List [ Sexp.Atom "par"; Sexp.List params ] :: conses) ->
          (params, conses)
      | Sexp.List conses -> ([], conses)
      | _ -> failwith @@ "Invalid datatype body: " ^ Sexp.to_string_hum body
    in
    (* Dependencies are free sort occurrences, not term names or parameters.
       Counting every atom invents recursive SCCs (a constructor named like an
       unrelated datatype links the two) and captures par-bound names (a local
       parameter spelled like a group member). Walk complete field sorts,
       including nested arguments. *)
    let rec sort_mentions acc = function
      | Sexp.Atom name as sort ->
          if
            List.mem names name ~equal:String.equal
            && not (List.mem bound sort ~equal:Stdlib.( = ))
          then Set.add acc name
          else acc
      | Sexp.List (Sexp.Atom "_" :: _) -> acc
      | Sexp.List sorts -> List.fold sorts ~init:acc ~f:sort_mentions
    in
    List.fold conses ~init:Set.Poly.empty ~f:(fun acc -> function
      | Sexp.Atom _ -> acc
      | Sexp.List (_name :: fields) ->
          List.fold fields ~init:acc ~f:(fun acc -> function
            | Sexp.List [ _selector; sort ] -> sort_mentions acc sort
            | field ->
                failwith @@ "Invalid datatype field: "
                ^ Sexp.to_string_hum field)
      | cons ->
          failwith @@ "Invalid datatype constructor: " ^ Sexp.to_string_hum cons)
  in
  let deps =
    Map.Poly.of_alist_exn
    @@ List.map2_exn names bodies ~f:(fun n b -> (n, mentions b))
  in
  (* a component is a set of names that reach each other; with the groups this
     reader sees being small, the reachability is computed directly *)
  let rec reach seen n =
    if Set.mem seen n then seen
    else
      Set.fold ~init:(Set.add seen n) ~f:reach
      @@ Option.value (Map.Poly.find deps n) ~default:Set.Poly.empty
  in
  let reaches n = reach Set.Poly.empty n in
  let same n m = Set.mem (reaches n) m && Set.mem (reaches m) n in
  let comps =
    List.fold names ~init:[] ~f:(fun comps n ->
        if List.exists comps ~f:(fun c -> List.mem c n ~equal:String.equal) then
          comps
        else comps @ [ List.filter names ~f:(same n) ])
  in
  (* A component comes after everything it mentions, emitted by repeatedly
     taking the components whose dependencies are all placed.  Sorting with a
     comparator instead looks shorter and is wrong: "mentions" is a partial
     order, a comparator built from it is not transitive, and the sort then
     produces an order that satisfies no one -- which is how the first version
     of this put a wrapper before the type it wraps. *)
  let rec order placed remaining =
    if List.is_empty remaining then []
    else
      let ready, blocked =
        List.partition_tf remaining ~f:(fun c ->
            let needs = Set.Poly.union_list @@ List.map c ~f:reaches in
            Set.for_all needs ~f:(fun n ->
                List.mem c n ~equal:String.equal
                || List.mem placed n ~equal:String.equal))
      in
      if List.is_empty ready then
        (* Unreachable: a cycle between components is what makes them one
           component.  Emitting the rest in their declared order rather than
           looping keeps a future change to the component computation from
           turning a bug into a hang. *)
        remaining
      else ready @ order (placed @ List.concat ready) blocked
  in
  let ordered = order [] comps in
  List.map ordered ~f:(fun c ->
      List.filter_map (List.zip_exn names bodies) ~f:(fun (n, b) ->
          if List.mem c n ~equal:String.equal then Some (n, b) else None))

let mk_new_datatypes ~print uni_sort dtenv dts funcs flag =
  let datatypes =
    List.map2_exn funcs dts ~f:(fun func -> function
      | Sexp.List [ Sexp.Atom name; Sexp.Atom n ] ->
          let arity = index_numeral ~what:"datatype arity" n in
          let params =
            match func with
            | Sexp.List (Sexp.Atom "par" :: Sexp.List params :: _)
            | Sexp.List (Sexp.List [ Sexp.Atom "par"; Sexp.List params ] :: _)
              ->
                List.map (sort_parameters_of_sexp ~what:"datatype" params)
                  ~f:(fun p -> Sort.SVar p)
            | _ when arity = 0 -> []
            | _ ->
                failwith
                @@ sprintf "Invalid datatype declaration: %s"
                     (Sexp.to_string_hum func)
          in
          if List.length params <> arity then
            failwith
            @@ sprintf
                 "[datatype] %s declares arity %d but binds %d parameter(s)"
                 name arity (List.length params);
          (params, Datatype.mk_dt name params)
      | _ ->
          failwith
          @@ sprintf "Invalid datatype declaration: %s"
               (Sexp.to_string_hum func))
  in
  let datatypes =
    List.map2_exn datatypes funcs ~f:(fun (params, dt) -> function
      | Sexp.List [ Sexp.Atom "par"; Sexp.List _; Sexp.List conses ]
      | Sexp.List (Sexp.List [ Sexp.Atom "par"; Sexp.List _ ] :: conses)
      | Sexp.List conses ->
          let conses =
            List.fold_left ~init:[] conses ~f:(fun conses cons ->
                mk_dt_cons ~print uni_sort dtenv (Some params) dt
                  (List.map ~f:snd datatypes)
                  cons
                :: conses)
          in
          { dt with conses }
      | _ -> assert false)
  in
  List.map datatypes ~f:(fun dt ->
      Datatype.make (Datatype.name_of_dt dt) datatypes flag)

let mk_old_datatypes ~print uni_sort dtenv dts flag params =
  let params =
    List.map (sort_parameters_of_sexp ~what:"datatype" params) ~f:(fun p ->
        Sort.SVar p)
  in
  let datatypes =
    List.map dts ~f:(function
      | Sexp.List (Sexp.Atom name :: _) -> (params, Datatype.mk_dt name params)
      | _ -> assert false)
  in
  let datatypes =
    List.map2_exn datatypes dts ~f:(fun (params, dt) -> function
      | Sexp.List (_ :: conses) ->
          let conses =
            List.fold_left conses ~init:[] ~f:(fun conses cons ->
                mk_dt_cons ~implicit_params:true ~print uni_sort dtenv
                  (Some params) dt
                  (List.map ~f:snd datatypes)
                  cons
                :: conses)
          in
          { dt with conses }
      | _ -> assert false)
  in
  List.map datatypes ~f:(fun dt ->
      Datatype.make (Datatype.name_of_dt dt) datatypes flag)

(* Report the sorts that [sort_of_sexp] defaulted to [Sort.SVar] but that turn out,
   once the whole file has been read, to name a datatype: such an occurrence was a
   forward reference and is now a sort variable, which does not unify with the
   datatype at the application sites (Z3 reports "Sort mismatch ... #svar_<name>"). *)
let check_forward_referenced_sorts ~print (envs : Problem.envs) =
  let svs_of_senv =
    Map.Poly.fold ~init:Set.Poly.empty ~f:(fun ~key:_ ~data:sort acc ->
        Set.union acc @@ Term.svs_of_sort sort)
  in
  let svs =
    Set.Poly.union_list
      [
        svs_of_senv envs.uni_senv;
        svs_of_senv envs.exi_senv;
        Set.Poly.union_list
        @@ List.map ~f:(snd >> Term.svs_of_sort)
        @@ List.concat @@ Map.Poly.data envs.dep_map;
      ]
  in
  Set.iter svs ~f:(fun sv ->
      if not (Set.mem envs.uni_sort (Sort.SVar sv)) then
        let name = Ident.name_of_svar sv in
        match DTEnv.look_up_dt envs.dtenv name with
        | None -> () (* already reported by [warn_undeclared_sort] *)
        | Some _ ->
            print
            @@ lazy
                 (sprintf
                    "[warning] \"%s\" is used as a sort before its datatype \
                     declaration and was therefore parsed as a sort variable; \
                     move the declare-datatypes for \"%s\" before that use, or \
                     the solver will report a sort mismatch on \"%s\" \
                     applications"
                    name name name))

(* A symbol declared under the satisfiability reading is an ordinary uninterpreted symbol: it
   enters the signature with no kind, which is how [declare-const] has always been handled.
   Under the synthesis reading it is an unknown and its kind follows the result sort -- Bool is
   a relation, Int and Real are the function kinds the templates provide, and a regular
   expression is a value rather than a function, so only a nullary one can be synthesised.
   Anything else has no template and is refused by name, but now only where synthesis was
   actually asked for, which is the point of the split.  The universally quantified reading of a
   symbol has its own keyword, [declare-forall-fun], so nothing needs this one to provide it. *)
(* Sugar that turns a declaration into a premise -- a cardinality assumption, a law on a
   universally quantified function -- is defined by rewriting the rest of the input, so that
   what the solver and the solution checker see is the problem one would have written by hand.
   Two pieces are shared by every such expansion. *)

(* does this s-expression mention any of these symbols? the premise is inserted only into the
   assertions that do, so a clause that never speaks of the symbol is left as it was *)
let sexp_mentions names =
  (* one hash set per partial application, not a list scan per atom: under the dependents'
     reading the list holds every Bool unknown, hundreds of names, and every atom of every
     assertion was compared with each of them, once per law (on a 643-assertion input with
     20 laws and 472 unknowns that was most of a 100 s reading); the answer is the same *)
  let set = Hash_set.of_list (module String) names in
  let rec go = function
    | Sexp.Atom a -> Hash_set.mem set a
    | Sexp.List es -> List.exists es ~f:go
  in
  go

(* The symbols through which a command can reach one of [names]: [names] themselves and,
   transitively, every definition ([define-fun], [define-fun-rec], [define-funs-rec],
   [define-const]) among [es] whose body mentions a symbol already in the set.  An assertion
   that applies such a definition speaks of the symbol as surely as one that writes it, since
   the definition is inlined or unfolded into it; a front end that routes a trait method through
   one definition per implementation writes the symbol nowhere else.  The test is syntactic, as
   [sexp_mentions] is: a definition parameter spelled like a reached symbol also counts, which
   only adds premises and is harmless for the reason given at the [:law] expansion.  The order
   of the commands is ignored, so a fixpoint covers mutual recursion. *)
let names_reaching names es =
  let defs =
    List.concat_map es ~f:(function
      | Sexp.List
          [
            Sexp.Atom ("define-fun" | "define-fun-rec");
            Sexp.Atom d;
            _;
            _;
            body;
          ] ->
          [ (d, body) ]
      | Sexp.List [ Sexp.Atom "define-const"; Sexp.Atom d; _; body ] ->
          [ (d, body) ]
      | Sexp.List [ Sexp.Atom "define-funs-rec"; Sexp.List decls; Sexp.List bodies ]
        -> (
          match
            List.zip
              (List.map decls ~f:(function
                | Sexp.List (Sexp.Atom d :: _) -> Some d
                | _ -> None))
              bodies
          with
          | Ok pairs ->
              List.filter_map pairs ~f:(fun (d, b) ->
                  Option.map d ~f:(fun d -> (d, b)))
          | Unequal_lengths -> [] (* refused where the command is read *))
      | _ -> [])
  in
  let rec fix names =
    let mentions = sexp_mentions names in
    let added =
      List.filter_map defs ~f:(fun (d, body) ->
          if (not (List.mem names d ~equal:String.( = ))) && mentions body
          then Some d
          else None)
    in
    if List.is_empty added then names
    else fix (List.dedup_and_sort ~compare:String.compare (names @ added))
  in
  fix names

(* Whether a [:law] premise also reaches the assertions that apply an unknown whose dependency set
   contains the law's function.  On, for every reader of an [.smt2] file whatever the backend: it is
   the reading the laws state, and the reading without it is unsound for [unsat] (it demands a
   dependent clause for unlawful interpretations too, so a problem the laws make satisfiable can
   read as unsatisfiable).  [false] only in a test comparing the two readings.  Process-wide, and
   only ever read while a file is being read, which happens before any solver domain exists.

   Why: an unknown that depends on a universal function [f] is, after reading, applied to [f]
   as an argument, so an assertion that applies it speaks of [f] as surely as one that writes
   [f]; but it writes [f] nowhere, so the direct-mention test leaves the law out of it.  The
   clause is then demanded for the unlawful interpretations of [f] as well -- for a loop head
   whose invariant must say [hist_inv(f0, g)], the clause entering the loop asks the invariant to
   hold at [g = f0] for every relation [hist_inv], reflexive or not, which no invariant mentioning
   it can do, and argument filtering then erases [f] from the unknown altogether, since nothing
   constrains it there.  Inserting the premise is sound for the reason given at the [:law]
   expansion: more premises move the expanded problem toward the stated one, never past it. *)
let law_reaches_dependents = ref true

(* The unknowns among [es] that depend on [name], [es] being the commands after [name]'s
   declaration.

   Contract: [p] is returned exactly when the reader, reading [p]'s declaration, puts [name] in
   [p]'s dependency set -- the set whose members become [p]'s leading arguments.  The reader has
   two places that build one, and this mirrors both:
   - [declare-dep-exists-fun p (Y1 .. Yk) ...]: the set is [{Y1 .. Yk}], universals of any
     result sort, so [p] depends on [name] iff [name] is listed;
   - a plain [declare-fun p (...) Bool] under the synthesis reading: the set is every universal
     already declared that has a Bool result (the universals [kind_map] holds), so [p] depends on
     [name] iff [name] is Bool-valued, [p] being declared after it.  A universal constant or a
     function of another result sort is never in a default set; it reaches an unknown only by
     being listed or passed as an ordinary argument, and an ordinary argument is a mention.
   No other declaration builds a dependency set: a [declare-fun] of a non-Bool result, a
   [declare-const] and the kinded declarations ([declare-wfp] and the like) have none, and under
   the satisfiability reading ([synthesize = false]) a [declare-fun] is an uninterpreted symbol
   with none.  An over-approximation here would only add premises (sound, as said at
   [law_reaches_dependents]); an under-approximation would leave a dependent clause demanded for
   the unlawful interpretations, which is what this set exists to prevent. *)
let dependents_of ~bool_valued ~synthesize name es =
  List.filter_map es ~f:(function
    | Sexp.List
        [
          Sexp.Atom "declare-dep-exists-fun";
          Sexp.Atom p;
          Sexp.List deps;
          _;
          Sexp.Atom "Bool";
        ]
      when List.exists deps ~f:(function
             | Sexp.Atom d -> String.(d = name)
             | _ -> false) ->
        Some p
    | Sexp.List [ Sexp.Atom "declare-fun"; Sexp.Atom p; _; Sexp.Atom "Bool" ]
      when bool_valued && synthesize ->
        Some p
    | _ -> None)

(* Whether a [:law] premise inserted into an assertion leaves out the conjuncts the assertion
   already has as an antecedent.  On by default (an exact rewrite); PCSat's [law_dedup_premises =
   false] turns it off and re-reads the input.  Set only before a file is read.

   Why: one law is often attached to several functions (a trait's laws to each of its methods, at
   each type instance), and the expansion inserts it once per function reaching the assertion, so
   an assertion reached by three of them carries three copies; the law text itself may repeat a
   conjunct.  Every premise conjunct is a quantified formula the zero-unknown check instantiates,
   and copies multiply its instances without adding anything.  Exact: [c => (c' => phi)] with
   [c'] a conjunction containing [c] is [c => (c'' => phi)], [c''] the rest of [c'], and
   [c => phi] is [c /\ c => phi]; conjuncts are compared as s-expressions under the same binders,
   so only syntactic copies are dropped. *)
let law_dedup_premises = ref true

(* the conjuncts of a premise, [and]s flattened, left to right *)
let rec sexp_conjuncts = function
  | Sexp.List (Sexp.Atom "and" :: cs) -> List.concat_map cs ~f:sexp_conjuncts
  | c -> [ c ]

(* the conjuncts of the antecedents of the chain of implications [(=> p1 (=> p2 ... body))] at the
   top of [phi] *)
let rec antecedent_conjuncts = function
  | Sexp.List [ Sexp.Atom "=>"; p; body ] ->
      sexp_conjuncts p @ antecedent_conjuncts body
  | _ -> []

(* [premise] without the conjuncts [phi] already assumes (or that occur earlier in [premise]);
   [None] when nothing is left *)
let fresh_premise ~premise phi =
  let have = antecedent_conjuncts phi in
  let kept =
    List.fold (sexp_conjuncts premise) ~init:[] ~f:(fun acc c ->
        if List.mem have c ~equal:Sexp.equal || List.mem acc c ~equal:Sexp.equal
        then acc
        else c :: acc)
    |> List.rev
  in
  match kept with
  | [] -> None
  | [ c ] -> Some c
  | cs ->
      if List.length cs = List.length (sexp_conjuncts premise) then Some premise
      else Some (Sexp.List (Sexp.Atom "and" :: cs))

(* [sexp] with [premise] added, as [assert_with_premise] adds it to an assertion that mentions
   one of its names, and the premise actually inserted ([None] when nothing is inserted: the
   command is not an assertion, or every conjunct is already assumed) *)
let insert_premise ~premise sexp =
  let imply premise phi =
    if not !law_dedup_premises then
      (Sexp.List [ Sexp.Atom "=>"; premise; phi ], Some premise)
    else
      match fresh_premise ~premise phi with
      | None -> (phi, None)
      | Some p -> (Sexp.List [ Sexp.Atom "=>"; p; phi ], Some p)
  in
  match sexp with
  | Sexp.List [ Sexp.Atom "assert"; Sexp.List [ Sexp.Atom "forall"; bs; body ] ]
    ->
      let body, inserted = imply premise body in
      ( Sexp.List
          [
            Sexp.Atom "assert"; Sexp.List [ Sexp.Atom "forall"; bs; body ];
          ],
        inserted )
  | Sexp.List [ Sexp.Atom "assert"; phi ] ->
      let phi, inserted = imply premise phi in
      (Sexp.List [ Sexp.Atom "assert"; phi ], inserted)
  | e -> (e, None)

(* add [premise] to an assertion, under its own [forall] when it has one, so that a law written
   with the clause's variable names is instantiated at them rather than nested; with
   [law_dedup_premises], only the conjuncts it does not already assume *)
let assert_with_premise ~names ~premise =
  let mentions = sexp_mentions names in
  fun sexp -> if not (mentions sexp) then sexp else fst (insert_premise ~premise sexp)

(* every atom of an s-expression, into [set] *)
let rec add_sexp_atoms set = function
  | Sexp.Atom a -> Hash_set.add set a
  | Sexp.List es -> List.iter es ~f:(add_sexp_atoms set)

(* [List.fold laws ~init:es ~f:(fun es (names, premise) -> List.map es ~f:(assert_with_premise
   ~names ~premise))], the expansion of a run of [:law] declarations one after another, with
   each assertion scanned once instead of once per law: an assertion's atoms are collected
   once and grown by the atoms of each premise inserted into it, which are exactly the atoms
   the rewritten assertion gains ([=>] and the premise), so "mentions one of [names]" is
   answered from the set as [sexp_mentions] answers it from the text.  A command other than an
   assertion is never rewritten, so it is passed over.  On a generated input with 58 laws in
   front of a thousand commands of 4.7 MB, the per-law rescans were the larger half of the
   reading. *)
let assert_with_premises laws es =
  match laws with
  | [] -> es
  | [ (names, premise) ] -> List.map es ~f:(assert_with_premise ~names ~premise)
  | _ ->
      let laws =
        List.map laws ~f:(fun (names, premise) ->
            (List.dedup_and_sort ~compare:String.compare names, premise))
      in
      List.map es ~f:(function
        | Sexp.List (Sexp.Atom "assert" :: _) as sexp ->
            let atoms = Hash_set.create (module String) in
            add_sexp_atoms atoms sexp;
            List.fold laws ~init:sexp ~f:(fun sexp (names, premise) ->
                if not (List.exists names ~f:(Hash_set.mem atoms)) then sexp
                else
                  let sexp, inserted = insert_premise ~premise sexp in
                  (match inserted with
                  | None -> ()
                  | Some p ->
                      Hash_set.add atoms "=>";
                      add_sexp_atoms atoms p);
                  sexp)
        | e -> e)

let kind_of_synthesis_target ~fun_sort ~args_sort sret =
  if Term.is_bool_sort sret then Kind.Ord
  else if Term.is_int_sort sret then Kind.IntFun
  else if Term.is_real_sort sret then Kind.RealFun
  else if Term.is_regex_sort sret && List.is_empty args_sort then Kind.RegEx
  else
    (* a sort this tool cannot synthesise a function of: an honest limit of
       coverage, refused in one line rather than raised as an internal failure
       that the command line would print with a backtrace *)
    Common.Refusal.refuse "synthesis of a function of the sort %s is not supported"
      (Term.str_of_sort fun_sort)

(* Predicate kinds in this reader's extended syntax.  A kind is a condition on
   one solution rather than a constraint, so plain SMT-LIB has nowhere to put
   it, and a file that declares a kinded unknown with [declare-fun] states a
   weaker problem than the one it names.  Each kind is therefore a declaration
   command of its own, and the SMT-LIB2 printer writes exactly these, so a
   printed problem reads back as itself:

     (declare-fnp    P (S1 ... Sn) Bool)   functional
     (declare-wfp    P (S1 ... Sn) Bool)   well-founded
     (declare-totp (i1 ... ik) P (S1 ... Sn) Bool)
                                           total over the universally quantified
                                           positions i1..ik (0-based, distinct):
                                           at every value of them some value of
                                           the others satisfies P
     (declare-nep    P (S1 ... Sn) Bool)   non-empty, read as (declare-totp () ...);
                                           the printer writes the declare-totp form
     (declare-dwfp   P (S1 ... Sn) Bool)   disjunctively well-founded
     (declare-integp P (S1 ... Sn) Bool)   integrable
     (declare-admp   P (S1 ... Sn) Bool)   admissible, without conditioning
     (declare-admcp  P (S1 ... Sn) Bool)   admissible, with conditioning
     (declare-uniqp  j prov P (S1 ... Sn) Bool)
                                           single-valued at position j (0-based),
                                           prov one of declared, entailed,
                                           least-model
     (declare-nwfp    F l r P (S1 ... Sn) Bool)   member (l, r) of an NWF family
     (declare-parityp F l r P (S1 ... Sn) Bool)   member (l, r) of a parity family

   A family [F] is written in full in every member, so a member can be read
   without any state beyond what is already declared.  The two kinds share
   [Kind.nwf] as a record and not as a meaning, so their families differ:

     NWF     (N (shared S...) (tags (t (S...)) ...))
     parity  (N (tags (t (S...)) ...) (max-priority k)
                (priority (t i) ...) (accepting i ...) (truncation identity|halve))

   An NWF family is an encoding device -- a decrease stated by a guard at the
   predicate application rather than by threading the old state through the
   arguments -- so it is the shared sorts and the per-tag sorts and nothing
   else; it has no priorities, and its producers fill those fields with
   placeholders nobody reads.  A parity family is a parity progress relation,
   and its priorities, accepting set and truncation are what make it one
   (Kura and Unno, "Solving First-Order Fixed-Point Logics via a
   Least-to-Greatest Transformation Based on Game Semantics", Defs. 2.10, 3.1
   and 7.8): a tag is a predicate of one strongly connected component, its
   priority is the reassigned one, the accepting set is the priorities at
   which a non-strict decrease is allowed, [max-priority] is the number of
   ranking components, and [truncation] maps a priority to the number of
   components it compares -- the identity, or halving rounded up when the
   components are packed in pairs; it names one of the two functions the
   fixpoint reduction builds, since a closure cannot be written.  A parity
   relation relates the disjoint union of its tags' domains, so it has no
   shared sorts.  Every tag has a priority, and truncating it gives at most
   [max-priority] components, since the template indexes its components by
   that number.

   Every member naming [N] must carry the same family, and [P]'s argument
   sorts must be the shared sorts followed by the two tags' sorts, which is
   the arity every consumer of the family assumes.  [P] itself must be the
   name the family gives the member -- [N_{l,r}] for NWF and
   [N_{l@i,r@j}] for parity, [i] and [j] the tags' priorities -- because the
   cycle learner rebuilds that name from the family when it states what it
   learned, and a member declared under any other name would receive clauses
   about a predicate that does not exist. *)
let simple_kind_of_command = function
  | "declare-nep" -> Some (Kind.Tot [])
  | "declare-dwfp" -> Some Kind.DWF
  | "declare-integp" -> Some Kind.Integ
  | "declare-admp" -> Some (Kind.Adm Kind.Adm_expectation)
  | "declare-admcp" -> Some (Kind.Adm Kind.Adm_conditional)
  | "declare-admpp" -> Some (Kind.Adm Kind.Adm_probability)
  | "declare-admlp" -> Some (Kind.Adm Kind.Adm_liberal)
  | _ -> None

let halve_truncation i = if i mod 2 = 0 then i / 2 else (i + 1) / 2

let nwf_of_sexp ~print ~parity uni_sort dtenv = function
  | Sexp.List (Sexp.Atom name :: fields) ->
      let keys =
        List.filter_map fields ~f:(function
          | Sexp.List (Sexp.Atom k :: _) -> Some k
          | _ -> None)
      in
      let allowed =
        if parity then
          [ "tags"; "max-priority"; "priority"; "accepting"; "truncation" ]
        else [ "shared"; "tags" ]
      in
      List.iter keys ~f:(fun k ->
          if not (List.mem allowed k ~equal:String.equal) then
            failwithf
              "the family %s: an %s family has no (%s ...) field%s" name
              (if parity then "parity" else "NWF")
              k
              (if parity then "; a parity relation shares no sorts"
               else "; priorities belong to a parity family")
              ());
      let field key =
        match
          List.find_map fields ~f:(function
            | Sexp.List (Sexp.Atom k :: v) when String.equal k key -> Some v
            | _ -> None)
        with
        | Some v -> v
        | None ->
            failwithf "the family %s has no (%s ...) field" name key ()
      in
      let sort s =
        Logic.ExtTerm.of_old_sort (sort_of_sexp ~print uni_sort dtenv None s)
      in
      let int_of = function
        | Sexp.Atom a -> (
            match Int.of_string_opt a with
            | Some i -> i
            | None -> failwithf "the family %s: %s is not an integer" name a ())
        | e ->
            failwithf "the family %s: %s is not an integer" name
              (Sexp.to_string e) ()
      in
      let sorts_map = Hashtbl.Poly.create () in
      List.iter (field "tags") ~f:(function
        | Sexp.List [ Sexp.Atom t; Sexp.List ss ] ->
            Hashtbl.Poly.set sorts_map ~key:(Ident.Tvar t)
              ~data:(List.map ss ~f:sort)
        | e ->
            failwithf "the family %s: %s is not a (tag (sorts)) pair" name
              (Sexp.to_string e) ());
      let max_pri, sigma, trunc, acc_set =
        if not parity then
          (* the placeholders every NWF producer fills in *)
          (0, Map.Poly.empty, Fn.id, Set.Poly.empty)
        else
      let max_pri =
        match field "max-priority" with
        | [ a ] -> int_of a
        | _ -> failwithf "the family %s: (max-priority k) takes one integer" name ()
      in
      let sigma =
        Map.Poly.of_alist_exn
        @@ List.map (field "priority") ~f:(function
          | Sexp.List [ Sexp.Atom p; i ] -> (Ident.Tvar p, int_of i)
          | e ->
              failwithf "the family %s: %s is not a (predicate priority) pair"
                name (Sexp.to_string e) ())
      in
      let trunc =
        match field "truncation" with
        | [ Sexp.Atom "identity" ] -> Fn.id
        | [ Sexp.Atom "halve" ] -> halve_truncation
        | _ ->
            failwithf
              "the family %s: (truncation ...) is identity or halve, the two \
               functions the fixpoint reduction builds"
              name ()
      in
      let acc_set = Set.Poly.of_list @@ List.map (field "accepting") ~f:int_of in
      Hashtbl.Poly.iter_keys sorts_map ~f:(fun t ->
          match Map.Poly.find sigma t with
          | None ->
              failwithf "the family %s: the tag %s has no priority" name
                (Ident.name_of_tvar t) ()
          | Some i when i < 1 || trunc i > max_pri ->
              failwithf
                "the family %s: the tag %s has priority %d, which is not \
                 between 1 and what %d components can compare"
                name (Ident.name_of_tvar t) i max_pri ()
          | Some _ -> ());
      Map.Poly.iter_keys sigma ~f:(fun t ->
          if not (Hashtbl.Poly.mem sorts_map t) then
            failwithf "the family %s: %s has a priority and is not a tag" name
              (Ident.name_of_tvar t) ());
      (max_pri, sigma, trunc, acc_set)
      in
      Kind.
        {
          name = Ident.Tvar name;
          sorts_shared =
            (if parity then [] else List.map (field "shared") ~f:sort);
          sorts_map;
          max_pri;
          sigma;
          trunc;
          acc_set;
          priority_switch = None;
        }
  | e -> failwithf "%s is not a family (name fields...)" (Sexp.to_string e) ()

(* two readings of one family must agree; the truncation is compared on every
   priority it can be applied to, since a closure has no other equality *)
let same_nwf (n1 : Kind.nwf) (n2 : Kind.nwf) =
  let alist n =
    List.sort ~compare:Stdlib.compare @@ Hashtbl.Poly.to_alist n.Kind.sorts_map
  in
  Stdlib.(n1.Kind.sorts_shared = n2.Kind.sorts_shared)
  && Stdlib.(alist n1 = alist n2)
  && n1.max_pri = n2.max_pri
  && Map.Poly.equal Int.equal n1.sigma n2.sigma
  && Set.equal n1.acc_set n2.acc_set
  && List.for_all
       (List.init (n1.max_pri + 3) ~f:Fn.id)
       ~f:(fun i -> n1.trunc i = n2.trunc i)

(* [(P ((x1 S1) ... (xn Sn)) (A1 ... Ak))] of a [(set-info :candidates ...)],
   added to [envs.candidates] after the entries already read for [P].  Refused
   with a message naming the declaration when [P] is not a declared unknown,
   (for an unknown declared with a dependency set, the parameters are its
   written arguments; the dependencies are prepended under their own names),
   when the binders do not have [P]'s argument sorts, or when an atom is not a
   Boolean formula over the binders and the problem's shared symbols. *)
let candidate_atoms_of_sexp ~print ~inline (envs : Problem.envs) decl =
  let refuse why =
    failwith
    @@ sprintf "[set-info :candidates] %s: %s" why (Sexp.to_string decl)
  in
  match decl with
  | Sexp.List [ Sexp.Atom name; Sexp.List binders; Sexp.List atoms ] ->
      let p = Ident.Tvar name in
      let arg_sorts =
        match Map.Poly.find envs.exi_senv p with
        | Some sort when Map.Poly.mem envs.kind_map p -> Sort.args_of sort
        | _ -> refuse (name ^ " is not a declared unknown")
      in
      let xs =
        try List.map binders ~f:(bind_of_sexp ~print envs.uni_sort envs.dtenv)
        with exn_ when not (Common.Timer.is_async exn_) ->
          refuse "the parameters are not a list of (name sort)"
      in
      (* an unknown with a dependency set takes the universal functions in it
         as its leading arguments ([declare-dep-exists-fun]); the declaration
         lists only the written ones, and an atom names a dependency by the
         function's own name, which is the name of that parameter here *)
      let xs =
        match Map.Poly.find envs.dep_map p with
        | Some deps when List.length xs + List.length deps = List.length arg_sorts
          ->
            deps @ xs
        | _ -> xs
      in
      if
        List.length xs <> List.length arg_sorts
        || not
             (List.for_all2_exn xs arg_sorts ~f:(fun (_, s1) s2 ->
                  Stdlib.(s1 = s2)))
      then refuse (sprintf "the parameters do not have the sorts of %s" name);
      (match
         List.find_a_dup xs ~compare:(fun (x, _) (y, _) ->
             Ident.tvar_compare x y)
       with
      | Some (x, _) -> refuse (Ident.name_of_tvar x ^ " is bound twice")
      | None -> ());
      let envs_atoms =
        {
          envs with
          uni_senv =
            List.fold xs ~init:envs.uni_senv ~f:(fun acc (x, s) ->
                Map.Poly.set acc ~key:x ~data:s);
        }
      in
      (* no unknown and no variable other than the parameters, the
         problem's shared symbols and the functions it defines
         ([define-fun-rec]): a defined function is applied as a variable of
         the term language but is not a free symbol -- its definition fixes
         it in every model -- so an atom such as [c = cnt s i] is a legal
         candidate over the parameters [s], [i] and [c] *)
      let allowed =
        Set.Poly.union_list
          [
            Set.Poly.of_list (List.map xs ~f:fst);
            Map.key_set envs.uni_senv;
            Map.key_set envs.fenv;
          ]
      in
      let phis =
        List.map atoms ~f:(fun a ->
            let phi =
              try
                Typeinf.typeinf_formula ~print ~default:None ~to_sus:true
                  ~rigid:(rigid_of envs.uni_sort)
                @@ of_formula ~print ~inline envs_atoms a
              with exn_ when not (Common.Timer.is_async exn_) ->
                refuse
                  (sprintf "the atom %s is not a formula here (%s)"
                     (Sexp.to_string a) (Exn.to_string exn_))
            in
            if not (Set.is_empty (Formula.pvs_of phi)) then
              refuse
                (sprintf "the atom %s applies an unknown" (Sexp.to_string a));
            (match
               Set.find (Formula.tvs_of phi) ~f:(Fn.non (Set.mem allowed))
             with
            | Some v ->
                refuse
                  (sprintf "the atom %s mentions %s, which is not a parameter"
                     (Sexp.to_string a) (Ident.name_of_tvar v))
            | None -> ());
            phi)
      in
      {
        envs with
        candidates =
          Map.Poly.update envs.candidates p ~f:(function
            | None -> (xs, phis)
            | Some (xs0, phis0) ->
                (* a later declaration for the same unknown is read over its
                   own parameter names and renamed onto the first one's *)
                let ren =
                  Map.Poly.of_alist_exn
                  @@ List.map2_exn xs xs0 ~f:(fun (x, _) (x0, _) -> (x, x0))
                in
                (xs0, phis0 @ List.map phis ~f:(Formula.rename ren)));
      }
  | _ -> refuse "expected (P ((x S) ...) (atom ...))"

(* Function declarations and definitions share a source namespace even
   though their internal bindings live in different maps. This is a top-level
   introduction check; formal parameters and sort names are separate.  A
   redeclaration is an ill-formed input (z3 and cvc5 both reject it), so it is
   refused as an input this tool does not handle rather than raised as an
   internal failure: the command-line entry prints a refusal as one [error:]
   line, and an uncaught [Failure] as a backtrace. *)
let ensure_function_name_fresh ~what (envs : Problem.envs) name =
  ensure_declarable_symbol ~what name;
  let key = Ident.Tvar name in
  if Map.Poly.mem envs.fenv key then
    Common.Refusal.refuse "[%s] function %s is already defined" what name;
  if Map.Poly.mem envs.exi_senv key then
    Common.Refusal.refuse "[%s] function %s is already declared" what name

(* Aliases and datatype/uninterpreted declarations introduce sort symbols in
   one source namespace. Check the whole group before resolving any bodies;
   local par parameters and term names occupy separate binding contexts.  A
   theory sort counts as declared: [(declare-sort Int 0)] is rejected by z3
   ("sort already defined") and by cvc5 ("previously declared as a type"), and
   is refused here the same way as a function redeclaration above. *)
let ensure_sort_names_fresh ~what (envs : Problem.envs) names =
  ignore
  @@ List.fold names ~init:Set.Poly.empty ~f:(fun seen name ->
      ensure_declarable_symbol ~what name;
      if
        Set.mem seen name
        || List.mem theory_sort_names name ~equal:String.equal
        || Hashtbl.mem (sort_aliases ()) name
        || Option.is_some (DTEnv.look_up_dt envs.dtenv name)
        || Set.mem envs.uni_sort (Sort.SVar (Ident.Svar name))
      then Common.Refusal.refuse "[%s] sort %s is already declared" what name;
      Set.add seen name)

let ensure_datatype_sort_names_fresh ~what envs declarations =
  ensure_sort_names_fresh ~what envs
  @@ List.map declarations ~f:(function
    | Sexp.List (Sexp.Atom name :: _) -> name
    | sexp ->
        failwith
        @@ sprintf "[%s] invalid datatype declaration: %s" what
             (Sexp.to_string_hum sexp))

(* The SMT-LIB 2.6 assertion stack (the standard's section 4.1.4), as far as a
   reader that hands its caller ONE problem can keep it.

   What the standard says: [(push n)] adds n levels; [(pop n)] removes the n
   most recent ones and with them every assertion, declaration and definition
   made since -- the declarations survive only under
   [(set-option :global-declarations true)]; [(reset-assertions)] empties the
   stack, keeping only global declarations; [(reset)] returns to the state at
   start-up; [(check-sat-assuming (l ...))] checks the current assertions
   together with the literals, which are NOT asserted and are gone after the
   check; commands after [(exit)] are not executed.  Each [check-sat] asks
   about the assertions in scope at that point, and only there.

   What the caller gets: the assertions and the environment in scope at ONE
   check, its literals included.  With [stop_at = Some k] that is the [k]-th
   [check-sat] or [check-sat-assuming] (counted from 1, as [count_checks]
   counts them), and nothing after it is read, as a solver answering the
   checks in order has read nothing after the one it answers; with [None] it
   is the LAST check, or the end of the input when there is none.  A caller
   that answers every check reads the input once per check with [Some k]
   ([-p smt] does, each in a process of its own, because solving sets
   process-global environments); a caller that answers one problem reads it
   with [None].  Reading the whole file as one conjunction, as this reader
   once did, answers no check at all as soon as one is retracted: a [pop]
   that removes [x < 0] before asserting [x > 0], or two [check-sat-assuming]
   with opposite literals, was read as [unsat] where every check is [sat].

   [frames] holds, innermost first, what a [pop] restores: the assertions, the
   environment and the sort aliases at the matching [push].  Process state
   outside the environment -- the lemma and measure registries -- is not
   scoped. *)
type command_frame = {
  saved_acc : Formula.t list;
  saved_envs : Problem.envs;
  saved_aliases : (string, Ident.svar list * Sort.t) Hashtbl.t;
}

type command_state = {
  initial_envs : Problem.envs;
  mutable frames : command_frame list;
  mutable global_declarations : bool;
  mutable checked : (Formula.t list * Problem.envs) option;
  stop_at : int option;  (** the check to answer; [None] for the last *)
  mutable checks_seen : int;  (** the checks read so far *)
}

let command_state_key : command_state option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_command_state ?stop_at (envs : Problem.envs) f =
  let saved = Stdlib.Domain.DLS.get command_state_key in
  Stdlib.Domain.DLS.set command_state_key
    (Some
       {
         initial_envs = envs;
         frames = [];
         global_declarations = false;
         checked = None;
         stop_at;
         checks_seen = 0;
       });
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set command_state_key saved)
    f

let command_state () =
  match Stdlib.Domain.DLS.get command_state_key with
  | Some st -> st
  | None -> failwith "[toplevel] the command state is not initialised"

(* the level count of [push]/[pop]: a numeral, and 1 when omitted (z3 and cvc5
   accept the bare form) *)
let scope_levels ~what = function
  | [] -> 1
  | [ Sexp.Atom n ] -> index_numeral ~what n
  | args ->
      Common.Refusal.refuse "[%s] expects one numeral, got %s" what
        (Sexp.to_string_hum (Sexp.List args))

(* A check has been read with [state] in scope: record it, and return the
   commands still to read [es] -- none once it is the check asked for. *)
let check_reached state es =
  let st = command_state () in
  st.checks_seen <- st.checks_seen + 1;
  st.checked <- Some state;
  match st.stop_at with Some k when st.checks_seen >= k -> [] | _ -> es

(* The number of [check-sat] and [check-sat-assuming] commands before the
   first [(exit)], counted as [toplevel] counts them for [stop_at]. *)
let count_checks sexps =
  let rec go n = function
    | [] | Sexp.List [ Sexp.Atom "exit" ] :: _ -> n
    | Sexp.List [ Sexp.Atom "check-sat" ] :: es
    | Sexp.List [ Sexp.Atom "check-sat-assuming"; Sexp.List _ ] :: es ->
        go (n + 1) es
    | _ :: es -> go n es
  in
  go 0 sexps

(* A reader that answers ONE problem per input -- the constraint-solving entry,
   whose HORN logic has one check by convention -- answers the last check of a
   file with several (see [command_state]).  It says so on standard error, once
   per file and process however often the file is read again, so that stdout
   keeps only the answer. *)
let several_checks_warned : string list Atomic.t = Atomic.make []

let warn_if_several_checks ~filename sexps =
  let n = count_checks sexps in
  let warned = Atomic.get several_checks_warned in
  if n > 1 && not (List.mem warned filename ~equal:String.equal) then
    if Atomic.compare_and_set several_checks_warned warned (filename :: warned)
    then
      eprintf
        "[warning] %s has %d checks; only the last one is answered (one answer \
         per check is -p smt's)\n\
         %!"
        filename n

(* [(! t :named n)] names [t]: SMT-LIB 2.6 (section 3.6.5) gives it the effect
   of [(define-fun n () s t)] for the sort [s] of [t], and requires [t] to be
   closed, so [n] may be used by any later command -- typically
   [(check-sat-assuming (n))] or a later assertion.  The annotation itself
   denotes [t], which the term readers keep; what they cannot do is extend the
   scope, so the names of one command are defined here, before the command is
   read, innermost first so that a named term may contain a named term.  A
   term that cannot be read in the command's scope (it is not closed, which
   the standard forbids) defines nothing, as before. *)
let define_named_terms ~print ~inline (envs : Problem.envs) sexp =
  let rec named acc = function
    | Sexp.List (Sexp.Atom "!" :: t :: attrs) ->
        let acc = named acc t in
        let rec names acc = function
          | Sexp.Atom ":named" :: Sexp.Atom n :: rest -> names ((n, t) :: acc) rest
          | _ :: rest -> names acc rest
          | [] -> acc
        in
        names acc attrs
    | Sexp.List es -> List.fold es ~init:acc ~f:named
    | Sexp.Atom _ -> acc
  in
  List.fold (List.rev (named [] sexp)) ~init:envs ~f:(fun envs (n, t) ->
      (* a name already in use is an ill-formed input; the annotation is then
         read as before, as the term it wraps, and the name keeps its binding *)
      if is_term_symbol_bound envs n then envs
      else
      match
        Typeinf.typeinf_term ~print ~default:None ~to_sus:true
          ~rigid:(rigid_of envs.uni_sort)
          (of_term ~print ~inline envs t)
      with
      | exception exn_ when not (Common.Timer.is_async exn_) -> envs
      | term ->
          let sort = Term.sort_of term in
          let body =
            if Term.is_bool_sort sort then
              T_bool.of_formula (Formula.of_bool_term term)
            else term
          in
          {
            envs with
            fenv =
              Map.Poly.add_exn envs.fenv ~key:(Ident.Tvar n)
                ~data:([], sort, body, false, Formula.mk_true ());
          })

(* Whether each assertion's positive existentials are offered a witness drawn from the
   clause's own premises before the assertion is read ([premise_witness_disjuncts]).
   Process-wide, off by default, and only ever read while a file is being read, which happens
   before any solver domain exists. *)
let premise_witness_disjuncts = ref false

(* the most witness disjuncts one existential is given *)
let max_premise_witnesses = 4

(** [premise_witness_disjuncts_of ~is_def phi] is [(phi', n)]: the assertion [phi] with each
    existential [exists xs. B] at positive polarity replaced by
    [(exists ys1. B s1) \/ ... \/ (exists ysk. B sk) \/ exists xs. B], and [n] the number of
    disjuncts added (at most [max_premise_witnesses] per existential).  Each [si] maps some
    of [xs] to terms; [ysi] are the [xs] it leaves.

    Exact, in every model for well-sorted, capture-avoiding [si]: [B si] implies [exists xs. B]
    (take each bound variable to its image), so the added disjuncts are implied by the one
    kept, and the disjunction is equivalent to it.  Both verdicts of the problem read are
    therefore verdicts of the problem written.  The substitution is capture-avoiding because
    an [si] is used only when no variable of its terms is bound inside [B] or among [xs], and
    it stops at an inner binder that rebinds a variable it maps. Parallel let
    RHSs use the outer mapping; declarations, sorts and indices are preserved.
    Bodies with match, annotations or extension binders are left unchanged.
    [prepare_argument f i sort rhs] certifies a replacement at the bound sort
    using the definition's formal rank, and returns its rank-preserving syntax;
    without that certificate the candidate is declined. A Real formal can
    accept an Int actual, so matching application positions alone is not enough.

    Which [si].  [B]'s conjuncts that apply a defined function [P] ([is_def]) at some of [xs]
    are matched against the applications of the same [P] in the clause's premises (atoms at
    negative polarity, reached from the root through [not], [and], [or], [=>] and the
    outermost [forall]s only, so their terms are in scope at the existential): [x := a] for
    each bound [x] written as the argument at a position where the premise writes [a].  The
    other arguments are not compared.  The shape this is for: a loop's postcondition
    [exists s last fin. produces(it, s, last) /\ completed(last, fin) /\ r = len s] whose
    witness is the loop invariant's own [produces(it0, hist, cur)] in the premise, [s := hist]
    and [last := cur].  Once the definitions are inlined, the bodies of the two applications
    no longer share a term the witness can be read from, and the instantiation search the
    solver is then left with took tens of seconds where the instance alone is proved at
    once.  Only the existentials reached from the root through the same connectives are
    rewritten; the rest of the assertion, a [let] or an annotation included, is kept as
    written. *)
let premise_witness_disjuncts_of
    ?(prepare_argument = fun _ _ _ _ -> None) ~is_def phi =
  let atoms_of =
    let rec go acc = function
      | Sexp.Atom a -> Set.add acc a
      | Sexp.List l -> List.fold l ~init:acc ~f:go
    in
    go String.Set.empty
  in
  (* every name an inner binder ([forall], [exists], [let]) of [e] binds *)
  let rec binders_of acc = function
    | Sexp.Atom _ -> acc
    | Sexp.List
        ((Sexp.Atom ("forall" | "exists" | "let") :: Sexp.List bs :: _) as l) ->
        let acc =
          List.fold bs ~init:acc ~f:(fun acc -> function
            | Sexp.List (Sexp.Atom x :: _) -> Set.add acc x
            | _ -> acc)
        in
        List.fold l ~init:acc ~f:binders_of
    | Sexp.List l -> List.fold l ~init:acc ~f:binders_of
  in
  (* Only descend through term syntax whose scopes are handled below. Match
     patterns need datatype ranks; annotations may contain scoped patterns,
     and extension binders have their own rules. Keep their original formula
     rather than manufacture an instance with an unverified substitution. *)
  let rec supported = function
    | Sexp.Atom _ -> true
    | Sexp.List (Sexp.Atom ("match" | "lambda" | "random" | "!") :: _) -> false
    | Sexp.List es -> List.for_all es ~f:supported
  in
  let without_bindings m bs =
    List.fold bs ~init:m ~f:(fun m -> function
      | Sexp.List (Sexp.Atom x :: _) -> Map.remove m x
      | _ -> m)
  in
  (* The reader also accepts an array variable in application-head position.
     Its substitution would require a sort-directed select, not a renamed
     function head. Decline such mappings until that extension is handled. *)
  let rec supported_mapping m = function
    | Sexp.Atom _ -> true
    | Sexp.List [ Sexp.Atom ("forall" | "exists"); Sexp.List bs; body ] ->
        supported_mapping (without_bindings m bs) body
    | Sexp.List [ Sexp.Atom "let"; Sexp.List bs; body ] ->
        List.for_all bs ~f:(function
          | Sexp.List [ _; rhs ] -> supported_mapping m rhs
          | _ -> false)
        && supported_mapping (without_bindings m bs) body
    | Sexp.List (Sexp.Atom "_" :: _)
    | Sexp.List [ Sexp.Atom "as"; _; _ ] -> true
    | Sexp.List (head :: args) ->
        let mapped_head =
          match head with
          | Sexp.Atom name
          | Sexp.List [ Sexp.Atom "as"; Sexp.Atom name; _ ] -> Map.mem m name
          | _ -> false
        in
        not mapped_head && List.for_all args ~f:(supported_mapping m)
    | Sexp.List [] -> true
  in
  let rec subst m = function
    | Sexp.Atom a as e -> Option.value (Map.find m a) ~default:e
    | Sexp.List
        [ (Sexp.Atom ("forall" | "exists") as q); (Sexp.List bs as binds); body ] ->
        Sexp.List [ q; binds; subst (without_bindings m bs) body ]
    | Sexp.List [ (Sexp.Atom "let" as q); Sexp.List bs; body ] ->
        (* Let bindings are parallel: each RHS sees the outer mapping, while
           the body hides every bound name. Names themselves never change. *)
        let bs' =
          List.map bs ~f:(function
            | Sexp.List [ name; rhs ] -> Sexp.List [ name; subst m rhs ]
            | binding -> binding)
        in
        Sexp.List [ q; Sexp.List bs'; subst (without_bindings m bs) body ]
    | Sexp.List [ Sexp.Atom "as"; Sexp.Atom name; _ ] as e ->
        (* Qualification's sort is a different namespace. A mapped term
           already has that rank, so its qualifier is no longer needed. *)
        Option.value (Map.find m name) ~default:e
    | Sexp.List (Sexp.Atom "_" :: _) as e -> e
    | Sexp.List (head :: args) ->
        Sexp.List (head :: List.map args ~f:(subst m))
    | Sexp.List [] as e -> e
  in
  let is_app = function
    | Sexp.List (Sexp.Atom f :: _ :: _) -> is_def f
    | _ -> false
  in
  (* the defined-function applications at negative polarity *)
  let rec premises pos acc = function
    | Sexp.List [ Sexp.Atom "not"; e ] -> premises (not pos) acc e
    | Sexp.List (Sexp.Atom ("and" | "or") :: es) ->
        List.fold es ~init:acc ~f:(premises pos)
    | Sexp.List (Sexp.Atom "=>" :: (_ :: _ :: _ as es)) ->
        let hyps, concl = List.split_n es (List.length es - 1) in
        let acc = List.fold hyps ~init:acc ~f:(premises (not pos)) in
        List.fold concl ~init:acc ~f:(premises pos)
    | e when (not pos) && is_app e -> e :: acc
    | _ -> acc
  in
  let rec conj_apps = function
    | Sexp.List (Sexp.Atom "and" :: es) -> List.concat_map es ~f:conj_apps
    | e when is_app e -> [ e ]
    | _ -> []
  in
  let added = ref 0 in
  let witnesses prems binds body =
    let xs =
      List.filter_map binds ~f:(function
        | Sexp.List [ Sexp.Atom x; _ ] -> Some x
        | _ -> None)
    in
    if List.length xs <> List.length binds || not (supported body) then []
    else
      let blocked = Set.union (binders_of String.Set.empty body) (String.Set.of_list xs) in
      let subs =
        List.concat_map (conj_apps body) ~f:(function
          | Sexp.List (Sexp.Atom f :: args) ->
              List.filter_map prems ~f:(function
                | Sexp.List (Sexp.Atom g :: pargs)
                  when String.equal f g && List.length pargs = List.length args -> (
                    let m =
                      List.foldi (List.zip_exn args pargs)
                        ~init:(Some String.Map.empty)
                        ~f:(fun position m (a, p) ->
                          match (m, a) with
                          | Some m, Sexp.Atom x when List.mem xs x ~equal:String.equal -> (
                              let prepared =
                                List.find_map binds ~f:(function
                                  | Sexp.List [ Sexp.Atom name; sort ]
                                    when String.equal name x ->
                                      prepare_argument f position sort p
                                  | _ -> None)
                              in
                              match prepared with
                              | None -> None
                              | Some p -> (
                                  match Map.find m x with
                                  | None -> Some (Map.set m ~key:x ~data:p)
                                  | Some p' when Sexp.equal p p' -> Some m
                                  | Some _ -> None))
                          | _ -> m)
                    in
                    match m with
                    | Some m
                      when (not (Map.is_empty m))
                           && supported_mapping m body
                           && Map.for_all m ~f:(fun t ->
                                  Set.is_empty (Set.inter (atoms_of t) blocked)) ->
                        Some m
                    | _ -> None)
                | _ -> None)
          | _ -> [])
      in
      let subs =
        List.take
          (List.dedup_and_sort subs ~compare:(Map.compare_direct Sexp.compare))
          max_premise_witnesses
      in
      List.map subs ~f:(fun m ->
          let rest =
            List.filter binds ~f:(function
              | Sexp.List [ Sexp.Atom x; _ ] -> not (Map.mem m x)
              | _ -> true)
          in
          let inst = subst m body in
          if List.is_empty rest then inst
          else Sexp.List [ Sexp.Atom "exists"; Sexp.List rest; inst ])
  in
  let rec rw prems pos = function
    | Sexp.List [ (Sexp.Atom "not" as n); e ] ->
        Sexp.List [ n; rw prems (not pos) e ]
    | Sexp.List ((Sexp.Atom ("and" | "or") as c) :: es) ->
        Sexp.List (c :: List.map es ~f:(rw prems pos))
    | Sexp.List ((Sexp.Atom "=>" as c) :: (_ :: _ :: _ as es)) ->
        let hyps, concl = List.split_n es (List.length es - 1) in
        Sexp.List
          ((c :: List.map hyps ~f:(rw prems (not pos)))
          @ List.map concl ~f:(rw prems pos))
    | Sexp.List [ Sexp.Atom "exists"; Sexp.List binds; body ] as e when pos -> (
        match witnesses prems binds body with
        | [] -> e
        | ws ->
            added := !added + List.length ws;
            Sexp.List ((Sexp.Atom "or" :: ws) @ [ e ]))
    | e -> e
  in
  let rec top = function
    | Sexp.List [ (Sexp.Atom "forall" as q); Sexp.List bs; body ] as original ->
        (* A bound array may occupy application-head position and shadow a
           global definition. Its rank is not the global function's rank. *)
        if List.exists bs ~f:(function
             | Sexp.List [ Sexp.Atom name; _ ] -> is_def name
             | _ -> true)
        then original
        else Sexp.List [ q; Sexp.List bs; top body ]
    | e -> rw (premises true [] e) true e
  in
  let phi' = top phi in
  (phi', !added)

let rec toplevel ~print ~inline acc (envs : Problem.envs) = function
  | [] ->
      (* what is answered is the state at the check asked for, see
         [command_state] *)
      let st = command_state () in
      (match st.stop_at with
      | Some k when st.checks_seen < k ->
          (* the caller counted a check this reading did not meet; answering
             another check's state instead would print one answer twice *)
          failwith
          @@ sprintf "[toplevel] check %d asked for, but the input has %d" k
               st.checks_seen
      | _ -> ());
      let acc, envs =
        match st.checked with Some state -> state | None -> (acc, envs)
      in
      let acc' =
        (* A [let] whose definition mentions a symbol to be *synthesized* has to
           be substituted away: the clause conversion and the predicate
           accounting downstream do not look inside a [LetTerm], so an unknown
           hidden behind one is an unknown they never see. That is not true of a
           symbol the model merely interprets -- an ordinary [declare-fun]
           constant under the satisfiability reading -- and expanding those lets
           costs dearly, because a chain of n definitions each mentioning the
           previous one becomes 2^n copies. So the set below is the synthesis
           targets rather than every declared symbol: a declaration form that
           asks for synthesis records a kind for the symbol, and one that does
           not records none, which is what makes the intersection the right set.
           It is intersected with [exi_senv] because [kind_map] also carries a
           kind for a universally quantified Bool-valued function, which is a
           term variable and not an unknown. *)
        let synthesis_targets =
          Set.inter (Map.key_set envs.exi_senv) (Map.key_set envs.kind_map)
        in
        Common.PhaseTime.with_phase "finish" @@ fun () ->
        let ph name f x = Common.PhaseTime.with_phase name (fun () -> f x) in
        List.map acc
          ~f:
            (ph "normalize-let" (Normalizer.normalize_let ~rename:true)
            >> ph "elim-let" (Formula.elim_let_with_unknowns synthesis_targets)
            >> ph "normalize" Normalizer.normalize)
      in
      LogicOld.set_inlined_defs
      @@ Map.Poly.filter envs.fenv ~f:(Quintuple.fth >> not);
      (*ToDo*)
      (* a definition read again keeps a property proved about it since
         ([LogicOld.merge_fenv_keeping_properties]) *)
      LogicOld.set_fenv
      @@ LogicOld.merge_fenv_keeping_properties
           (Map.Poly.filter envs.fenv ~f:Quintuple.fth)
      @@ LogicOld.get_fenv ();
      check_forward_referenced_sorts ~print envs;
      (acc', envs)
  | Sexp.List [ Sexp.Atom "set-logic"; Sexp.Atom logic ] :: es ->
      (* The logic says how a declared symbol is meant, when it says anything at all: a Horn or
         SyGuS problem declares the symbols it wants solved for, an ordinary SMT-LIB logic
         declares symbols a model interprets.  [ALL] and [ALL_SUPPORTED] name no theory
         restriction and are used by both kinds of file, so they leave the caller's choice
         alone.  A logic this reader cannot read is a refusal, one line naming the logic and
         the reason, never an exception the entry point prints as a crash. *)
      let envs =
        match logic_reading logic with
        | Synthesize -> { envs with Problem.decl_reading = Problem.Synthesize }
        | Any -> envs
        | Interpreted -> { envs with Problem.decl_reading = Problem.Uninterpreted }
        | Refused why ->
            Common.Refusal.refuse "[set-logic] logic %s is not supported: %s"
              logic why
      in
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "set-info"; Sexp.Atom ":candidates"; decl ] :: es ->
      (* Candidate atoms for an unknown, written

           (set-info :candidates (P ((x1 S1) ... (xn Sn)) (A1 ... Ak)))

         with [P] declared earlier and [S1 ... Sn] its argument sorts; each
         [Ai] is a formula over [x1 ... xn] and the symbols the whole problem
         declares.  They are hints for the hypothesis space and are never
         asserted, so they leave the set of solutions unchanged.  [set-info]
         with a keyword the standard does not define and an s-expression value
         is standard SMT-LIB, which is why the hint is not a command of its
         own: a solver that knows nothing of it may skip it (cvc5 does, in
         silence; z3 reports an error line for the value and goes on). *)
      let envs = candidate_atoms_of_sexp ~print ~inline envs decl in
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "set-info"; Sexp.Atom ":coar-lemma"; Sexp.Atom name ]
    :: es ->
      (* The same lemma by name:

           (define-fun L ((x Int) (y Int) (r Int)) Bool
             (=> (mult x y r) (mult (- x 1) y (- r y))))
           (set-info :coar-lemma L)

         read as [forall x y r. body].  A [define-fun] is a conservative
         definition and a symbol value is accepted silently by z3 and cvc5,
         where z3 reports an error line (and goes on) for the s-expression
         value of the form below; the meaning is the same. *)
      (match Map.Poly.find envs.fenv (Tvar name) with
      | Some (fargs, sret, body, false, _) when Term.is_bool_sort sret ->
          add_pred_lemma (Formula.forall fargs (Formula.of_bool_term body))
      | _ ->
          print
          @@ lazy
               (sprintf
                  "[set-info :coar-lemma] %s is not a Boolean define-fun; \
                   skipped"
                  name));
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "set-info"; Sexp.Atom ":coar-lemma"; phi ] :: es ->
      (* A lemma about the predicates of a CHC problem, written

           (set-info :coar-lemma
             (forall ((x Int) (y Int) (r Int))
               (=> (mult x y r) (mult (- x 1) y (- r y)))))

         after the [declare-fun]s of the predicates it names: a closed
         formula, read like an assertion, whose predicates are the declared
         unknowns.  It is a claim about the least solution, never a clause:
         only the relational proof search of MuCyc reads it, proves it by its
         own rules before using it, and drops it unproved; every other solver
         ignores it, so the file's meaning is its assertions alone.  [set-info]
         with a keyword the standard does not define and an s-expression value
         is standard SMT-LIB ([attribute_value ::= ( s_expr* )]), so other
         solvers may skip it; the [coar-] prefix marks the keyword as this
         tool's, so it cannot be taken for another tool's lemma syntax. *)
      let phi =
        Typeinf.typeinf_formula ~print ~default:None ~to_sus:true
          ~rigid:(rigid_of envs.uni_sort)
        @@ of_formula ~print ~inline envs phi
      in
      add_pred_lemma phi;
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "set-info"; Sexp.Atom ":lemma"; Sexp.Atom name ]
    :: es ->
      (* A lemma about recursive functions, written

           (define-fun L ((y1 S1) ... (yn Sn)) Bool phi)
           (set-info :lemma L)

         and read as the claim [forall y1 .. yn. phi].  Both commands are
         standard SMT-LIB and leave the problem's meaning unchanged for any
         solver: a [define-fun] is a conservative definition, and [set-info]
         with a keyword the standard does not define and a symbol value is
         skipped (z3 and cvc5 accept it silently, also in their strict
         modes).  Here the claim is registered as a candidate lemma, which
         is used only once proved: it is never the function's property by
         being written.  Anything else after [:lemma] is skipped with a
         diagnostic. *)
      (match Map.Poly.find envs.fenv (Tvar name) with
      | Some (fargs, sret, body, false, _) when Term.is_bool_sort sret ->
          add_user_lemma (fargs, Formula.of_bool_term body)
      | _ ->
          print
          @@ lazy
               (sprintf
                  "[set-info :lemma] %s is not a Boolean define-fun; skipped"
                  name));
      toplevel ~print ~inline acc envs es
  | Sexp.List (Sexp.Atom "set-info" :: Sexp.Atom name :: t :: _) :: es -> (
      (* The older, non-standard form [(set-info f (forall ys. phi))] that some
         copied benchmarks carry ([set-info] takes a keyword in SMT-LIB, so z3
         and cvc5 refuse it).  It was once stored as [f]'s property, which
         every query reaching [f] then assumed whether or not it was true; it
         is now a candidate lemma like the standard form above, used only once
         proved. *)
      match Map.Poly.find envs.fenv (Tvar name) with
      | Some _ ->
          let phi =
            Typeinf.typeinf_formula ~print ~default:None ~to_sus:true
              ~rigid:(rigid_of envs.uni_sort)
            @@ of_formula ~print ~inline envs t
          in
          (if Formula.is_forall phi then
             let _, env, body, _ = Formula.let_bind phi in
             add_user_lemma (env, body)
           else add_user_lemma ([], phi));
          toplevel ~print ~inline acc envs es
      | None -> toplevel ~print ~inline acc envs es (* ToDo: ignored? *))
  | Sexp.List
      [ Sexp.Atom "set-option"; Sexp.Atom ":global-declarations"; Sexp.Atom b ]
    :: es ->
      (command_state ()).global_declarations <- String.equal b "true";
      toplevel ~print ~inline acc envs es
  (* a check asks about the assertions in scope now; see [command_state] *)
  | Sexp.List [ Sexp.Atom "check-sat" ] :: es ->
      toplevel ~print ~inline acc envs (check_reached (acc, envs) es)
  | Sexp.List [ Sexp.Atom "check-sat-assuming"; Sexp.List lits ] :: es ->
      (* the literals take part in this check only and are not asserted *)
      let assumed =
        List.map lits ~f:(fun l ->
            Common.PhaseTime.with_phase "assert" @@ fun () ->
            of_formula ~print ~inline envs l)
      in
      toplevel ~print ~inline acc envs
        (check_reached (List.rev_append assumed acc, envs) es)
  (* nothing after [exit] is executed *)
  | Sexp.List [ Sexp.Atom "exit" ] :: _ -> toplevel ~print ~inline acc envs []
  | Sexp.List (Sexp.Atom "push" :: args) :: es ->
      let st = command_state () in
      for _level = 1 to scope_levels ~what:"push" args do
        st.frames <-
          {
            saved_acc = acc;
            saved_envs = envs;
            saved_aliases = Hashtbl.copy (sort_aliases ());
          }
          :: st.frames
      done;
      toplevel ~print ~inline acc envs es
  | Sexp.List (Sexp.Atom "pop" :: args) :: es ->
      let st = command_state () in
      let n = scope_levels ~what:"pop" args in
      if n = 0 then toplevel ~print ~inline acc envs es
      else if n > List.length st.frames then
        (* z3 and cvc5 both report an error for popping more levels than were
           pushed *)
        Common.Refusal.refuse "[pop] %d level(s) popped but only %d pushed" n
          (List.length st.frames)
      else
        let frame = List.nth_exn st.frames (n - 1) in
        st.frames <- List.drop st.frames n;
        if st.global_declarations then
          toplevel ~print ~inline frame.saved_acc envs es
        else (
          Stdlib.Domain.DLS.set sort_aliases_key frame.saved_aliases;
          toplevel ~print ~inline frame.saved_acc frame.saved_envs es)
  | Sexp.List [ Sexp.Atom "reset-assertions" ] :: es ->
      let st = command_state () in
      st.frames <- [];
      if st.global_declarations then toplevel ~print ~inline [] envs es
      else (
        Stdlib.Domain.DLS.set sort_aliases_key (Hashtbl.Poly.create ());
        (* the logic is not part of the assertion stack and stays set *)
        toplevel ~print ~inline []
          { st.initial_envs with Problem.decl_reading = envs.decl_reading }
          es)
  | Sexp.List [ Sexp.Atom "reset" ] :: es ->
      let st = command_state () in
      st.frames <- [];
      st.global_declarations <- false;
      Stdlib.Domain.DLS.set sort_aliases_key (Hashtbl.Poly.create ());
      toplevel ~print ~inline [] st.initial_envs es
  | Sexp.List (Sexp.Atom ("set-info" | "set-option") :: _) :: es
  | Sexp.List [ Sexp.Atom "get-model" ] :: es
  | Sexp.List (Sexp.Atom "check-sat-using" :: _) :: es ->
      toplevel ~print ~inline acc envs es (* ToDo: ignored? *)
  | Sexp.List [ Sexp.Atom "declare-forall-sort"; Sexp.Atom name ] :: es ->
      ensure_declarable_symbol ~what:"declare-forall-sort" name;
      let uni_sort' = Set.add envs.uni_sort (Sort.SVar (Ident.Svar name)) in
      toplevel ~print ~inline acc { envs with uni_sort = uni_sort' } es
  | Sexp.List
      [
        Sexp.Atom "declare-forall-sort";
        Sexp.Atom name;
        Sexp.Atom ":min-card";
        Sexp.Atom k;
      ]
    :: es ->
      (* sugar for a cardinality assumption: the sort
         is an ordinary forall-sort, [k] universal constants of it are
         declared, and their pairwise distinctness becomes a premise of every
         following assertion *that mentions one of them* — the same problem one
         would write by hand from a trait bound with k distinguished elements.
         Purely syntactic: the rest of the file is rewritten and re-read. *)
      let k = index_numeral ~what:"declare-forall-sort :min-card" k in
      if k < 2 then
        toplevel ~print ~inline acc envs
          (Sexp.List [ Sexp.Atom "declare-forall-sort"; Sexp.Atom name ] :: es)
      else
        let consts = List.init k ~f:(fun i -> sprintf "#card_%s_%d" name i) in
        let decls =
          List.map consts ~f:(fun c ->
              Sexp.List
                [
                  Sexp.Atom "declare-forall-fun";
                  Sexp.Atom c;
                  Sexp.List [];
                  Sexp.Atom name;
                ])
        in
        let premise =
          Sexp.List
            (Sexp.Atom "distinct" :: List.map consts ~f:(fun c -> Sexp.Atom c))
        in
        let with_premise = assert_with_premise ~names:consts ~premise in
        toplevel ~print ~inline acc envs
          (Sexp.List [ Sexp.Atom "declare-forall-sort"; Sexp.Atom name ]
           :: decls
          @ List.map es ~f:with_premise)
  | Sexp.List [ Sexp.Atom "declare-sort"; Sexp.Atom name; Sexp.Atom numeral ]
    :: es ->
      ensure_sort_names_fresh ~what:"declare-sort" envs [ name ];
      let dtenv' =
        DTEnv.update_dt envs.dtenv
        @@ Datatype.mk_uninterpreted_datatype ~numeral:(index_numeral ~what:"declare-sort arity" numeral)
             name
      in
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom "declare-datatypes"; Sexp.List args; Sexp.List dts ]
    :: es
    when List.for_all args ~f:(function Sexp.Atom _ -> true | _ -> false) ->
      ensure_datatype_sort_names_fresh ~what:"declare-datatypes" envs dts;
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_old_datatypes ~print envs.uni_sort envs.dtenv dts Datatype.FDt
             args
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom "declare-datatypes"; Sexp.List dts; Sexp.List funcs ]
    :: es ->
      ensure_datatype_sort_names_fresh ~what:"declare-datatypes" envs dts;
      let dtenv' =
        (* one declaration per strongly connected component, in dependency
           order, so that a member built over a sibling finds it already
           declared instead of having to defer the reference *)
        let name_of = function
          | Sexp.List (Sexp.Atom n :: _) -> n
          | s ->
              failwith
              @@ sprintf "Invalid datatype declaration: %s" (Sexp.to_string s)
        in
        List.fold
          (split_datatype_group (List.map dts ~f:name_of) funcs)
          ~init:envs.dtenv
          ~f:(fun env comp ->
            let names = List.map comp ~f:fst in
            let dts' =
              List.filter dts ~f:(fun d ->
                  List.mem names (name_of d) ~equal:String.equal)
            in
            List.fold_left ~init:env ~f:DTEnv.update_dt
            @@ mk_new_datatypes ~print envs.uni_sort env dts'
                 (List.map comp ~f:snd) Datatype.FDt)
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom "declare-codatatypes"; Sexp.List args; Sexp.List dts ]
    :: es
    when List.for_all args ~f:(function Sexp.Atom _ -> true | _ -> false) ->
      ensure_datatype_sort_names_fresh ~what:"declare-codatatypes" envs dts;
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_old_datatypes ~print envs.uni_sort envs.dtenv dts Datatype.FCodt
             args
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List
      [ Sexp.Atom "declare-codatatypes"; Sexp.List dts; Sexp.List funcs ]
    :: es ->
      ensure_datatype_sort_names_fresh ~what:"declare-codatatypes" envs dts;
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_new_datatypes ~print envs.uni_sort envs.dtenv dts funcs
             Datatype.FCodt
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom cmd; Sexp.Atom name; Sexp.List args; Sexp.Atom "Bool" ]
    :: es
    when Option.is_some (simple_kind_of_command cmd) ->
      ensure_function_name_fresh ~what:cmd envs name;
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args
                 ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name)
          ~data:(Option.value_exn (simple_kind_of_command cmd))
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom (("declare-nwfp" | "declare-parityp") as cmd);
        family;
        Sexp.Atom l;
        Sexp.Atom r;
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:cmd envs name;
      let nwf =
        (* Family/position validation below does not establish symbol freshness. *)
        nwf_of_sexp ~print
          ~parity:(String.equal cmd "declare-parityp")
          envs.uni_sort envs.dtenv family
      in
      Map.Poly.iter envs.kind_map ~f:(function
        | Kind.NWF (nwf', _) | Kind.Parity (nwf', _)
          when Kind.equal_nwf nwf nwf' && not (same_nwf nwf nwf') ->
            failwithf
              "%s: the family %s is defined differently by an earlier member" name
              (Ident.name_of_tvar nwf.name) ()
        | _ -> ());
      let tag_sorts t =
        match Hashtbl.Poly.find nwf.sorts_map (Ident.Tvar t) with
        | Some ss -> ss
        | None ->
            failwithf "%s: %s is not a tag of the family %s" name t
              (Ident.name_of_tvar nwf.name) ()
      in
      let arg_sorts =
        List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
      in
      let declared = List.map arg_sorts ~f:Logic.ExtTerm.of_old_sort in
      let expected = nwf.sorts_shared @ tag_sorts l @ tag_sorts r in
      if not Stdlib.(declared = expected) then
        failwithf
          "%s: a member of the family %s takes the shared sorts followed by \
           the sorts of its two tags"
          name
          (Ident.name_of_tvar nwf.name) ();
      let canonical =
        Ident.name_of_tvar
        @@
        if String.equal cmd "declare-nwfp" then
          Kind.nwf_tvar_of_nwf nwf.name (Ident.Tvar l) (Ident.Tvar r)
        else Kind.parity_tvar_of_nwf nwf (Ident.Tvar l) (Ident.Tvar r)
      in
      if not (String.equal name canonical) then
        failwithf
          "%s: a member (%s, %s) of the family %s must be named %s, the name \
           the family gives it"
          name l r
          (Ident.name_of_tvar nwf.name)
          canonical ();
      let kind =
        if String.equal cmd "declare-nwfp" then
          Kind.NWF (nwf, (Ident.Tvar l, Ident.Tvar r))
        else Kind.Parity (nwf, (Ident.Tvar l, Ident.Tvar r))
      in
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:(Sort.mk_fun @@ arg_sorts @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:kind
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-totp";
        Sexp.List positions;
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-totp" envs name;
      let arg_sorts =
        List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
      in
      let arity = List.length arg_sorts in
      let positions =
        List.map positions ~f:(function
          | Sexp.Atom a -> (
              match int_of_string_opt a with
              | Some i when i >= 0 && i < arity -> i
              | _ ->
                  failwithf
                    "%s: a universal position of a total predicate must be an \
                     argument index between 0 and %d, not %s"
                    name (arity - 1) a ())
          | e ->
              failwithf "%s: %s is not an argument position" name
                (Sexp.to_string e) ())
      in
      if List.contains_dup positions ~compare:Int.compare then
        failwithf "%s: a universal position of a total predicate is repeated"
          name ();
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:(Sort.mk_fun @@ arg_sorts @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name)
          ~data:(Kind.Tot (List.sort positions ~compare:Int.compare))
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-uniqp";
        Sexp.Atom j;
        Sexp.Atom prov;
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-uniqp" envs name;
      let arg_sorts =
        List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
      in
      let j =
        match int_of_string_opt j with
        | Some j when j >= 0 && j < List.length arg_sorts -> j
        | _ ->
            failwithf
              "%s: the position of a single-valued predicate must be an \
               argument index between 0 and %d"
              name
              (List.length arg_sorts - 1)
              ()
      in
      let prov =
        match Kind.provenance_of_string prov with
        | Some p -> p
        | None ->
            failwithf
              "%s: a single-valued predicate's provenance is declared, \
               entailed or least-model, not %s"
              name prov ()
      in
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:(Sort.mk_fun @@ arg_sorts @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name)
          ~data:(Kind.Uniq (j, prov))
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-fnp";
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-fnp" envs name;
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args
                 ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.FN
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-wfp";
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-wfp" envs name;
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args
                 ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.WF
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-fun";
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-fun" envs name;
      (*print @@ lazy ("adding " ^ name);*)
      (* under the satisfiability reading this is an uninterpreted predicate: no dependency
         set, no kind, just a symbol the model interprets *)
      let deps =
        match envs.decl_reading with
        | Problem.Uninterpreted -> []
        | Problem.Synthesize ->
            List.filter
              (Map.Poly.to_alist envs.uni_senv)
              ~f:(fst >> Map.Poly.mem envs.kind_map (*ToDo*))
      in
      let fun_sort =
        Sort.mk_fun @@ List.map deps ~f:snd
        @ List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
        @ [ T_bool.SBool ]
      in
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name) ~data:fun_sort
      in
      let dep_map' =
        match envs.decl_reading with
        | Problem.Uninterpreted -> envs.dep_map
        | Problem.Synthesize ->
            Map.Poly.add_exn envs.dep_map ~key:(Ident.Tvar name) ~data:deps
      in
      let kind_map' =
        match envs.decl_reading with
        | Problem.Uninterpreted -> envs.kind_map
        | Problem.Synthesize ->
            Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.Ord
      in
      toplevel ~print ~inline acc
        {
          envs with
          exi_senv = exi_senv';
          dep_map = dep_map';
          kind_map = kind_map';
        }
        es
  (* This is the *second* form that declares an unknown: under the synthesis
     reading a plain [declare-fun] is one, and so is this, so a count of the
     unknowns of a file taken by grepping [declare-fun] is wrong wherever this
     form appears.  Both write [exi_senv]; only this one also writes
     [dep_map]. *)
  | Sexp.List
      [
        Sexp.Atom "declare-dep-exists-fun";
        Sexp.Atom name;
        Sexp.List deps;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-dep-exists-fun" envs name;
      (*print @@ lazy ("adding " ^ name);*)
      let deps =
        (* the dependency set of a DQCHC unknown: every
           name must be a declared forall-fun, of any result sort.  The list
           is not filtered by [kind_map], which only Bool forall-funs enter:
           that would drop a universal constant or function named here
           without a word and change the verdict. *)
        let deps =
          Set.Poly.of_list
          @@ List.map deps ~f:(function
            | Sexp.Atom name -> Ident.Tvar name
            | _ -> assert false)
        in
        Set.iter deps ~f:(fun x ->
            if not (Map.Poly.mem envs.uni_senv x) then
              failwith
              @@ sprintf
                   "[declare-dep-exists-fun %s] %s is not a declared forall-fun"
                   name (Ident.name_of_tvar x));
        List.filter (Map.Poly.to_alist envs.uni_senv) ~f:(fun (x, _) ->
            Set.mem deps x)
      in
      let fun_sort =
        Sort.mk_fun @@ List.map deps ~f:snd
        @ List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
        @ [ T_bool.SBool ]
      in
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name) ~data:fun_sort
      in
      let dep_map' =
        Map.Poly.add_exn envs.dep_map ~key:(Ident.Tvar name) ~data:deps
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.Ord
      in
      toplevel ~print ~inline acc
        {
          envs with
          exi_senv = exi_senv';
          dep_map = dep_map';
          kind_map = kind_map';
        }
        es
  | Sexp.List [ Sexp.Atom "declare-fun"; Sexp.Atom name; Sexp.List args; ret ]
    :: es ->
      ensure_function_name_fresh ~what:"declare-fun" envs name;
      (*print @@ lazy ("adding " ^ name);*)
      let args_sort =
        List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
      in
      let sret = sort_of_sexp ~print envs.uni_sort envs.dtenv None ret in
      let fun_sort = Sort.mk_fun @@ args_sort @ [ sret ] in
      Ident.avoid_tvar (Ident.Tvar name);
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name) ~data:fun_sort
      in
      let kind_map' =
        match envs.decl_reading with
        | Problem.Uninterpreted -> envs.kind_map
        | Problem.Synthesize ->
            Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name)
              ~data:(kind_of_synthesis_target ~fun_sort ~args_sort sret)
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-forall-fun";
        Sexp.Atom name;
        Sexp.List args;
        ret;
        Sexp.Atom ":law";
        law;
      ]
    :: es ->
      (* Sugar for a law on a universally quantified function -- a trait law, in the source
         language this usually comes from.  The function is universal in every clause, so a law
         about it cannot be a top-level assertion: that would read as "this holds for *every*
         interpretation", which no interpretation satisfies.  It has to be a premise of the
         clauses that speak of the function, which is what this expands to.  Writing the law
         with the clause's own variable names instantiates it there; writing it closed, with its
         own [forall], nests it, which is always sound and costs the solver more.

         Purely syntactic, like the cardinality sugar above: the declaration becomes the plain
         one and the rest of the input is rewritten, so the solver and the solution checker see
         the problem one would have written by hand.

         Contract: the premise is inserted into exactly the following assertions that mention
         the function directly or through the transitive bodies of the definitions they apply
         ([names_reaching]), and with [law_reaches_dependents] also those that apply an unknown
         depending on it ([dependents_of]); what is inserted, and where, is the same in every
         case.  Inserting
         into more assertions never costs a solution.  The problem the law states is "for every
         interpretation of the function satisfying the law, the clauses hold".  A clause with
         the law as a premise sits between the bare clause and that reading: a closed law gives
         exactly that reading, an open one (written with the clause's variables) assumes one
         instance of it, which is weaker than assuming all of them, and in both cases the bare
         clause implies the guarded one.  So every solution of the problem with fewer premises
         solves the one with more, and every solution of the latter solves the intended problem.
         For an assertion that does not depend on the function at all the premise changes
         nothing whenever the law is satisfiable by some interpretation, since the clause must
         then hold for that one.  Leaving out an assertion that reaches the function through a
         definition, as the direct-mention test did, demanded the clause also for the unlawful
         interpretations, a problem stronger than the one stated. *)
      (* The run of [declare-forall-fun] commands this one starts is expanded at once, which is
         what expanding its laws one after another gives: a law rewrites only assertions, so
         the definitions and declarations each law's [names_reaching] and [dependents_of] read
         are the same before and after the earlier laws of the run, and each assertion is
         rewritten by the run's laws in their order ([assert_with_premises]). *)
      let law_of = function
        | Sexp.List
            [
              Sexp.Atom "declare-forall-fun";
              Sexp.Atom name;
              Sexp.List args;
              ret;
              Sexp.Atom ":law";
              law;
            ] ->
            Some (name, args, ret, law)
        | _ -> None
      in
      let rec split_run acc = function
        | (Sexp.List (Sexp.Atom "declare-forall-fun" :: _) as c) :: rest ->
            split_run (c :: acc) rest
        | rest -> (List.rev acc, rest)
      in
      let run, rest =
        split_run [] (Sexp.List
            [
              Sexp.Atom "declare-forall-fun"; Sexp.Atom name; Sexp.List args;
              ret; Sexp.Atom ":law"; law;
            ] :: es)
      in
      let rec expand plain laws = function
        | [] -> (List.rev plain, List.rev laws)
        | c :: later -> (
            match law_of c with
            | None -> expand (c :: plain) laws later
            | Some (name, args, ret, law) ->
                let es = later @ rest in
                let names =
                  Common.PhaseTime.with_phase "law-reach" @@ fun () ->
                  names_reaching
                    (name
                    ::
                    (if !law_reaches_dependents then
                       dependents_of
                         ~bool_valued:
                           (match ret with Sexp.Atom "Bool" -> true | _ -> false)
                         ~synthesize:
                           (match envs.decl_reading with
                           | Problem.Synthesize -> true
                           | Problem.Uninterpreted -> false)
                         name es
                     else []))
                    es
                in
                expand
                  (Sexp.List
                     [
                       Sexp.Atom "declare-forall-fun"; Sexp.Atom name;
                       Sexp.List args; ret;
                     ]
                  :: plain)
                  ((names, law) :: laws) later)
      in
      let plain, laws = expand [] [] run in
      toplevel ~print ~inline acc envs
        (plain
        @ Common.PhaseTime.with_phase "law-premise" (fun () ->
              assert_with_premises laws rest))
  | Sexp.List
      [ Sexp.Atom "declare-forall-fun"; Sexp.Atom name; Sexp.List args; ret ]
    :: es ->
      (* a universally quantified function or predicate (DQCHC): a term
         variable, universal in every clause.  With arguments it has array sort
         and an application is a [select] chain (a function-sorted variable
         could not cross the Z3 boundary); without arguments it is a universal
         constant of the result sort — the form a cardinality assumption's
         constants take.  Any result sort is
         accepted; only a Bool result is a predicate for [kind_map]. *)
      let sret = sort_of_sexp ~print envs.uni_sort envs.dtenv None ret in
      let sargs =
        List.map args ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
      in
      let sort =
        if List.is_empty sargs then sret
        else T_array.of_arrow @@ Sort.mk_fun (sargs @ [ sret ])
      in
      let uni_senv' =
        Map.Poly.add_exn envs.uni_senv ~key:(Ident.Tvar name) ~data:sort
      in
      let kind_map' =
        if Term.is_bool_sort sret then
          Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.Ord
        else envs.kind_map
      in
      toplevel ~print ~inline acc
        { envs with uni_senv = uni_senv'; kind_map = kind_map' }
        es
  | Sexp.List [ Sexp.Atom "declare-const"; Sexp.Atom name; ty ] :: es ->
      ensure_function_name_fresh ~what:"declare-const" envs name;
      (* SMT-LIB defines this as [(declare-fun name () ty)], so it must get the same reading;
         otherwise the very same declaration would be accepted in one spelling and refused
         in the other. *)
      let sret = sort_of_sexp ~print envs.uni_sort envs.dtenv None ty in
      (* a declared name this process would also mint has to stop being one it
         will mint: nothing here can be renamed, since the file refers to the
         declaration by that name *)
      Ident.avoid_tvar (Ident.Tvar name);
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name) ~data:sret
      in
      let kind_map' =
        match envs.decl_reading with
        | Problem.Uninterpreted -> envs.kind_map
        | Problem.Synthesize ->
            Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name)
              ~data:(kind_of_synthesis_target ~fun_sort:sret ~args_sort:[] sret)
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List [ Sexp.Atom "define-const"; Sexp.Atom name; ty; body ] :: es ->
      ensure_function_name_fresh ~what:"define-const" envs name;
      (* (define-const c ty t) abbreviates (define-fun c () ty t) *)
      toplevel ~print ~inline acc envs
        (Sexp.List
           [ Sexp.Atom "define-fun"; Sexp.Atom name; Sexp.List []; ty; body ]
        :: es)
  | Sexp.List
      [ Sexp.Atom "define-fun"; Sexp.Atom name; Sexp.List fargs; ty; body ]
    :: es ->
      ensure_function_name_fresh ~what:"define-fun" envs name;
      let fenv' =
        let fargs' =
          List.map fargs ~f:(bind_of_sexp ~print envs.uni_sort envs.dtenv)
        in
        let sort = sort_of_sexp ~print envs.uni_sort envs.dtenv None ty in
        let fargs', body_env, body = definition_scope envs name fargs' body in
        let body =
          Common.PhaseTime.with_phase "define-fun" @@ fun () ->
          definition_body ~print ~inline body_env sort body
        in
        Map.Poly.add_exn envs.fenv ~key:(Tvar name)
          ~data:(fargs', sort, body, false, Formula.mk_true ())
      in
      toplevel ~print ~inline acc { envs with fenv = fenv' } es
  | Sexp.List
      [ Sexp.Atom "define-fun-rec"; Sexp.Atom name; Sexp.List fargs; ty; body ]
    :: es ->
      ensure_function_name_fresh ~what:"define-fun-rec" envs name;
      let envs =
        { envs with
          lifted_universals =
            Map.Poly.remove envs.lifted_universals (Tvar name) }
      in
      let fenv', lifted_universals =
        let fargs' =
          List.map fargs ~f:(bind_of_sexp ~print envs.uni_sort envs.dtenv)
        in
        let sort = sort_of_sexp ~print envs.uni_sort envs.dtenv None ty in
        let body, measure = split_decreases body in
        let fargs', body_env, body, measure =
          definition_scope_with envs name fargs' body (Option.to_list measure)
        in
        register_measure name (List.hd measure)
          ~read:(definition_body ~print ~inline body_env T_int.SInt);
        let body =
          let fenv' =
            let body_rec =
              Term.mk_var (Tvar name) sort
              (*ToDo*)
            in
            Map.Poly.add_exn envs.fenv ~key:(Tvar name)
              ~data:(fargs', sort, body_rec, true, Formula.mk_true ())
          in
          let envs = { body_env with fenv = fenv' } in
          definition_body ~print ~inline envs sort body
        in
        let group, lifted_universals =
          lift_universals envs [ (name, fargs', sort, body) ]
        in
        let fargs', body =
          match group with
          | [ (_, fargs', _, body) ] -> (fargs', body)
          | _ -> assert false
        in
        ( Map.Poly.add_exn envs.fenv ~key:(Tvar name)
            ~data:(fargs', sort, body, true, Formula.mk_true ()),
          lifted_universals )
      in
      toplevel ~print ~inline acc { envs with fenv = fenv'; lifted_universals } es
  | Sexp.List [ Sexp.Atom "assert"; phi ] :: es ->
      let phi =
        if not !premise_witness_disjuncts then phi
        else
          let phi', n =
            premise_witness_disjuncts_of
              ~is_def:(fun f -> Map.Poly.mem envs.fenv (Ident.Tvar f))
              ~prepare_argument:(fun f position declared rhs ->
                match Map.Poly.find envs.fenv (Ident.Tvar f) with
                | None -> None
                | Some (params, _, _, _, _) -> (
                    match List.nth params position with
                    | None -> None
                    | Some (_, formal) -> (
                        try
                          let actual =
                            sort_of_sexp ~print:(fun _ -> ()) envs.uni_sort
                              envs.dtenv None declared
                          in
                          if not
                               (Sexp.equal (Datatype.structural_sort_key actual)
                                  (Datatype.structural_sort_key formal))
                          then None
                          else
                            match actual with
                            | T_real.SReal ->
                                (* The premise's Real slot may have accepted
                                   an Int term; retain the Real rank explicitly. *)
                                Some (Sexp.List [ Sexp.Atom "+"; Sexp.Atom "0.0"; rhs ])
                            | _ -> Some rhs
                        with exn when not (Common.Timer.is_async exn) -> None)))
              phi
          in
          for _ = 1 to n do
            Common.PhaseTime.event "reader-premise-witness"
          done;
          if n > 0 then
            print
            @@ lazy
                 (sprintf "[premise witness] %d witness disjunct(s) added" n);
          phi'
      in
      let envs = define_named_terms ~print ~inline envs phi in
      toplevel ~print ~inline
        ((Common.PhaseTime.with_phase "assert" @@ fun () ->
          of_formula ~print ~inline envs phi)
        :: acc)
        envs es
  (* extensions for CHCs *)
  | Sexp.List [ Sexp.Atom "declare-var"; Sexp.Atom name; sort ] :: es ->
      ensure_declarable_symbol ~what:"declare-var" name;
      let uni_senv' =
        Map.Poly.add_exn envs.uni_senv ~key:(Ident.Tvar name)
          ~data:(sort_of_sexp ~print envs.uni_sort envs.dtenv None sort)
      in
      toplevel ~print ~inline acc { envs with uni_senv = uni_senv' } es
  | Sexp.List [ Sexp.Atom "declare-rel"; Sexp.Atom name; Sexp.List args ] :: es
    ->
      ensure_function_name_fresh ~what:"declare-rel" envs name;
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args
                 ~f:(sort_of_sexp ~print envs.uni_sort envs.dtenv None)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.Ord
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List [ Sexp.Atom (("rule" | "query") as cmd); phi ] :: es ->
      (* Z3 Datalog syntax: [rule phi] asserts phi; [query phi] asserts that
         phi is unreachable, i.e. the goal clause [phi => false].  Both are
         closed over the declare-var variables they mention. *)
      let phi = of_formula ~print ~inline envs phi in
      let phi = if String.equal cmd "query" then Formula.mk_neg phi else phi in
      let bounds =
        List.filter_map
          (Set.to_list @@ Formula.fvs_of phi)
          ~f:(fun v ->
            match Map.Poly.find envs.uni_senv v with
            | None -> None
            | Some s -> Some (v, s))
      in
      toplevel ~print ~inline (Formula.mk_forall bounds phi :: acc) envs es
  (* ordinary SMT-LIB commands that carry no constraint and change no scope
     are skipped; the scope commands are read above *)
  | Sexp.List
      (Sexp.Atom
         (( "echo" | "get-info" | "get-option" | "get-value" | "get-assertions"
          | "get-assignment" | "get-proof" | "get-unsat-core"
          | "get-unsat-assumptions" | "get-objectives" ) as cmd)
      :: _)
    :: es ->
      print @@ lazy (sprintf "[toplevel] (%s ...) ignored" cmd);
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "define-sort"; Sexp.Atom name; Sexp.List ps; body ]
    :: es ->
      ensure_sort_names_fresh ~what:"define-sort" envs [ name ];
      let ps = sort_parameters_of_sexp ~what:"define-sort" ps in
      (* Resolve free sort names now, not under a later datatype's parameters.
         SMT-LIB aliases may contain their own parameters, not global ones. *)
      let body =
        sort_of_sexp ~print Set.Poly.empty envs.dtenv
          (Some (List.map ps ~f:(fun p -> Sort.SVar p)))
          body
      in
      Hashtbl.add_exn (sort_aliases ()) ~key:name ~data:(ps, body);
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "declare-datatype"; Sexp.Atom name; decl ] :: es ->
      (* SMT-LIB 2.7, section 4.2.3: the singular declaration abbreviates a
         one-member group whose arity is the number of written par binders.
         Validation stays in the group reader, including malformed formals. *)
      let arity =
        match decl with
        | Sexp.List (Sexp.Atom "par" :: Sexp.List params :: _)
        | Sexp.List (Sexp.List [ Sexp.Atom "par"; Sexp.List params ] :: _) ->
            List.length params
        | _ -> 0
      in
      toplevel ~print ~inline acc envs
        (Sexp.List
           [
             Sexp.Atom "declare-datatypes";
             Sexp.List
               [ Sexp.List [ Sexp.Atom name; Sexp.Atom (Int.to_string arity) ] ];
             Sexp.List [ decl ];
           ]
        :: es)
  | Sexp.List [ Sexp.Atom "define-funs-rec"; Sexp.List decls; Sexp.List bodies ]
    :: es ->
      (* every name is bound (to a placeholder, as define-fun-rec does for its
         own name) before any body is parsed, so mutual recursion resolves *)
      let decls =
        List.map decls ~f:(function
          | Sexp.List [ Sexp.Atom name; Sexp.List fargs; ty ] ->
              ( name,
                List.map fargs ~f:(bind_of_sexp ~print envs.uni_sort envs.dtenv),
                sort_of_sexp ~print envs.uni_sort envs.dtenv None ty )
          | sexp ->
              failwith @@ "[define-funs-rec] invalid declaration: "
              ^ Sexp.to_string_hum sexp)
      in
      if List.is_empty decls then
        failwith "[define-funs-rec] expected at least one declaration";
      let envs =
        { envs with
          lifted_universals =
            List.fold decls ~init:envs.lifted_universals
              ~f:(fun map (name, _, _) -> Map.Poly.remove map (Tvar name)) }
      in
      let fenv_placeholders =
        List.fold decls ~init:envs.fenv ~f:(fun fenv (name, fargs', sort) ->
            (* Check parsed names before reading any body. Only the completion
               fold below may replace this group's own placeholders. *)
            ensure_function_name_fresh ~what:"define-funs-rec"
              { envs with fenv } name;
            Map.Poly.add_exn fenv ~key:(Tvar name)
              ~data:
                ( fargs',
                  sort,
                  Term.mk_var (Tvar name) sort,
                  true,
                  Formula.mk_true () ))
      in
      let pairs =
        match List.zip decls bodies with
        | Ok pairs -> pairs
        | Unequal_lengths ->
            failwith
              "[define-funs-rec] declarations and bodies differ in number"
      in
      let group =
        List.map pairs ~f:(fun ((name, fargs', sort), body) ->
            let body, measure = split_decreases body in
            let fargs', envs, body, measure =
              definition_scope_with { envs with fenv = fenv_placeholders }
                name fargs' body (Option.to_list measure)
            in
            register_measure name (List.hd measure)
              ~read:(definition_body ~print ~inline envs T_int.SInt);
            let body =
              definition_body ~print ~inline envs sort body
            in
            (name, fargs', sort, body))
      in
      let group, lifted_universals = lift_universals envs group in
      let fenv' =
        List.fold group
          ~init:fenv_placeholders ~f:(fun fenv (name, fargs', sort, body) ->
            Map.Poly.set fenv ~key:(Tvar name)
              ~data:(fargs', sort, body, true, Formula.mk_true ()))
      in
      toplevel ~print ~inline acc
        { envs with fenv = fenv'; lifted_universals } es
  | sexps ->
      failwith @@ "parse error : " ^ Sexp.to_string_hum @@ Sexp.List sexps

(* Z3 predeclares a polymorphic list datatype -- (List T), with the constructors [nil] and
   [insert] and the selectors [head] and [tail] -- so a file written against Z3 uses "(List Int)"
   and never declares it.  SMT-LIB itself requires declaration before use, so without this the
   sort resolution stops at "unknown sort: (List Int)" and the whole file is unreadable, which is
   what 91 of the 105 constrained-Horn files of one ADT corpus did.  Note that the missing thing
   is the *declaration*: parametric datatypes are read, in both declaration syntaxes.

   It is seeded only when the input mentions [List] and binds no [List] of its own, because
   several inputs here do declare one, and with different constructors (nil/cons/hd/tl rather
   than nil/insert/head/tail).  The file's own declaration has to win, and the two sets of
   constructor names must not mix, so this must never overwrite a binding the input makes. *)
let builtin_list_datatypes ~print uni_sort dtenv =
  mk_old_datatypes ~print uni_sort dtenv
    [
      Sexp.List
        [
          Sexp.Atom "List";
          Sexp.Atom "nil";
          Sexp.List
            [
              Sexp.Atom "insert";
              Sexp.List [ Sexp.Atom "head"; Sexp.Atom "T" ];
              Sexp.List [ Sexp.Atom "tail"; Sexp.Atom "List" ];
            ];
        ];
    ]
    Datatype.FDt [ Sexp.Atom "T" ]

(* the sort names the input itself binds, by any of the commands that bind one *)
let rec sorts_bound_by = function
  | [] -> Set.Poly.empty
  | sexp :: es ->
      let here =
        match sexp with
        | Sexp.List [ Sexp.Atom "declare-sort"; Sexp.Atom name; _ ]
        | Sexp.List [ Sexp.Atom "declare-forall-sort"; Sexp.Atom name ]
        | Sexp.List [ Sexp.Atom "declare-forall-sort"; Sexp.Atom name; _ ]
        | Sexp.List [ Sexp.Atom "define-sort"; Sexp.Atom name; _; _ ]
        | Sexp.List [ Sexp.Atom "declare-datatype"; Sexp.Atom name; _ ] ->
            Set.Poly.singleton name
        | Sexp.List
            [
              Sexp.Atom ("declare-datatypes" | "declare-codatatypes");
              fst_;
              snd_;
            ] ->
            (* the 2.5 form names the datatypes in the second list, the 2.6 form in the
               first; taking the names out of both is what makes this independent of which *)
            let names_of = function
              | Sexp.List l ->
                  Set.Poly.of_list
                  @@ List.filter_map l ~f:(function
                    | Sexp.List (Sexp.Atom name :: _) -> Some name
                    | _ -> None)
              | _ -> Set.Poly.empty
            in
            Set.union (names_of fst_) (names_of snd_)
        | _ -> Set.Poly.empty
      in
      Set.union here (sorts_bound_by es)

let rec mentions_atom name = function
  | Sexp.Atom a -> String.(a = name)
  | Sexp.List l -> List.exists l ~f:(mentions_atom name)

let seed_builtin_datatypes ~print (envs : Problem.envs) sexps =
  let needed =
    (not (Option.is_some (DTEnv.look_up_dt envs.dtenv "List")))
    && (not (Set.mem (sorts_bound_by sexps) "List"))
    && List.exists sexps ~f:(mentions_atom "List")
  in
  if not needed then envs
  else begin
    print @@ lazy "[builtin] seeding Z3's predeclared (List T) datatype";
    {
      envs with
      dtenv =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ builtin_list_datatypes ~print envs.uni_sort envs.dtenv;
    }
  end

(* every entry point goes through [toplevel], so seeding here covers them all; the recursive
   calls inside the definition above still reach the unwrapped function, so the scan runs once
   per input rather than once per command *)
(* A printed problem names its variables with the very spellings this process
   mints for itself ([#tvar13]), so reading one back draws fresh names that can
   coincide with a name the file already binds.  Declarations step the counter
   past themselves as they are read, but a variable bound by a quantifier is met
   only while an assertion is being read, after earlier assertions have drawn
   names: a [let] binder renamed to [#tvar13] then shadowed a quantified
   [|#tvar13|] of sort [Int] inside the same body, and the conjunction failed
   type inference as [bool = int].  Stepping the counter past every atom of the
   input before anything is read closes the window for every binding form at
   once, and changes nothing on an input that does not use these spellings. *)
let rec avoid_generated_names = function
  | Sexp.Atom name -> Ident.avoid_tvar (Ident.Tvar name)
  | Sexp.List es -> List.iter es ~f:avoid_generated_names

(* The recursive parsers above share one expression scope. The exported
   term/formula APIs start independent scopes, including on nested calls. *)
let of_formula ~print ~inline envs phi =
  with_source_numeric_reader_scope @@ fun () ->
  avoid_generated_names phi;
  of_formula ~print ~inline envs phi

let of_term ~print ~inline envs term =
  with_source_numeric_reader_scope @@ fun () ->
  avoid_generated_names term;
  of_term ~print ~inline envs term

let toplevel ~print ~inline ?stop_at acc envs sexps =
  with_source_numeric_reader_scope @@ fun () ->
  with_sort_alias_scope @@ fun () ->
  List.iter sexps ~f:avoid_generated_names;
  let envs = seed_builtin_datatypes ~print envs sexps in
  with_command_state ?stop_at envs @@ fun () ->
  toplevel ~print ~inline acc envs sexps

(* Refuse a file that declares an unknown of a predicate kind other than the ordinary one.

   The plain-SMT entry point returns one formula, and a formula has no place for a kind: a
   [declare-wfp], [declare-fnp], [declare-nep], [declare-totp], [declare-uniqp], [declare-dwfp],
   [declare-nwfp], [declare-parityp], [declare-admp]/[declare-admcp] or [declare-integp] would be
   read as an ordinary uninterpreted predicate, and every consumer of that formula (the Z3 SMT
   solver, MuCyc's and MuStrat's SMT routes, the SMT printer) would answer a different problem.
   That is unsound, not incomplete: [(declare-wfp P (Int Int) Bool) (assert (P 0 0))] is
   unsatisfiable, since a well-founded relation relates no element to itself, and the dropped
   kind made it [sat].  No kind can be honoured exactly by one SMT query in general -- totality
   and non-emptiness are existence demands over every argument, well-foundedness is not
   first-order -- so the input is refused as unsupported, with the constraint solver named as the
   route that carries kinds.

   Only kinds of declared unknowns count: the reader also registers kinds for names that are not
   unknowns (the tag pairs of a non-well-founded family, the ordinary kind of a Bool universal),
   so the kind map is restricted to [exi_senv]. *)
let refuse_kinded_unknowns (envs : Problem.envs) =
  let kinded =
    Map.Poly.to_alist
    @@ Map.Poly.filteri envs.kind_map ~f:(fun ~key ~data ->
           (not (Kind.is_ord data)) && Map.Poly.mem envs.exi_senv key)
  in
  if not (List.is_empty kinded) then
    Common.Refusal.refuse
      "the plain SMT route reads a single formula, which carries no predicate \
       kinds, but this input declares %d unknown(s) of another kind: %s.  Use \
       the constraint solver (-p pcsp with a PCSat configuration)."
      (List.length kinded)
      (String.concat_map_list ~sep:", " kinded ~f:(fun (v, k) ->
           sprintf "%s (%s)" (Ident.name_of_tvar v) (Kind.str_of k)))

(* the plain-SMT entry point: a declared symbol is uninterpreted unless the file's [set-logic]
   asks for synthesis; an unknown of a predicate kind other than the ordinary one is refused
   (see [refuse_kinded_unknowns]).  [check] is the check whose problem is returned, counted
   from 1 as [count_checks] counts; the last one when omitted (see [command_state]). *)
let of_smt2_sexps ~print ~inline ?check ?(decl_reading = Problem.Uninterpreted)
    ?(uni_sort = Set.Poly.empty) ?(uni_senv = Map.Poly.empty)
    ?(exi_senv = Map.Poly.empty) ?(dep_map = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) ?(lifted_universals = Map.Poly.empty) sexps =
  let phis, _envs =
    toplevel ~print ~inline ?stop_at:check []
      {
        decl_reading;
        candidates = Map.Poly.empty;
        lifted_universals;
        uni_sort;
        uni_senv;
        exi_senv;
        dep_map;
        kind_map;
        fenv;
        dtenv;
      }
      sexps
  in
  refuse_kinded_unknowns _envs;
  let phi = Formula.and_of phis in
  print @@ lazy (sprintf "before typeinf: %s" @@ Formula.str_of phi);
  let phi' =
    Typeinf.typeinf_formula ~print ~default:None ~to_sus:true
      ~rigid:(rigid_of _envs.uni_sort) phi
  in
  print @@ lazy (sprintf "after typeinf: %s" @@ Formula.str_of phi');
  phi'

let read_smt2_sexps filename =
  In_channel.with_file filename ~f:(fun channel ->
      Parser.program Lexer.token (Lexing.from_channel channel))

let from_smt2_file ~print ~inline ?decl_reading ?uni_sort ?uni_senv ?exi_senv
    ?dep_map ?kind_map ?fenv ?dtenv ?lifted_universals filename =
  of_smt2_sexps ~print ~inline ?decl_reading ?uni_sort ?uni_senv ?exi_senv
    ?dep_map ?kind_map ?fenv ?dtenv ?lifted_universals
  @@ read_smt2_sexps filename

(* The probability threshold of a stochastic-SMT problem, written

     (set-info :threshold q)

   where [q] is a non-negative rational written as a numeral ([1]), a decimal
   ([0.5]), a fraction atom ([1/2]) or the term [(/ 1 2)].  A [(random ...)]
   quantifier gives a formula a probability, and the problem then asks whether
   that probability exceeds [q]; how strictly is the solver's contract, stated
   where the threshold is used.  [None] when the file states none: the caller's
   default applies.  A value that is not such a rational, a value outside
   [0, 1], or a second [:threshold] is refused with a one-line error rather
   than read as something else.  [set-info] with a keyword the standard does
   not define is standard SMT-LIB, so other solvers skip the line. *)
let threshold_of_sexps sexps =
  let numeral s =
    if (not (String.is_empty s)) && String.for_all s ~f:Char.is_digit then
      Some (Z.of_string s)
    else None
  in
  let rational_of_atom s =
    match String.lsplit2 s ~on:'/' with
    | Some (p, q) -> (
        match (numeral p, numeral q) with
        | Some p, Some q when not (Z.equal q Z.zero) -> Some (Q.make p q)
        | _ -> None)
    | None -> (
        match String.lsplit2 s ~on:'.' with
        | Some (i, f) -> (
            match (numeral i, numeral f) with
            | Some _, Some _ ->
                Some
                  (Q.make (Z.of_string (i ^ f))
                     (Z.pow (Z.of_int 10) (String.length f)))
            | _ -> None)
        | None -> Option.map (numeral s) ~f:Q.of_bigint)
  in
  let value_of = function
    | Sexp.Atom s -> rational_of_atom s
    | Sexp.List [ Sexp.Atom "/"; Sexp.Atom p; Sexp.Atom q ] -> (
        match (rational_of_atom p, rational_of_atom q) with
        | Some p, Some q when not (Q.equal q Q.zero) -> Some (Q.div p q)
        | _ -> None)
    | _ -> None
  in
  List.fold sexps ~init:None ~f:(fun acc -> function
    | Sexp.List [ Sexp.Atom "set-info"; Sexp.Atom ":threshold"; v ] -> (
        match (value_of v, acc) with
        | Some _, Some _ ->
            Common.Refusal.refuse "[set-info :threshold] is given twice"
        | Some q, None when Q.geq q Q.zero && Q.leq q Q.one -> Some q
        | Some q, None ->
            Common.Refusal.refuse
              "[set-info :threshold] %s is outside [0, 1]: a probability \
               threshold must lie between zero and one"
              (Q.to_string q)
        | None, _ ->
            Common.Refusal.refuse
              "[set-info :threshold] %s is not a rational number (write a \
               numeral, a decimal, p/q or (/ p q))"
              (Sexp.to_string v))
    | Sexp.List (Sexp.Atom "set-info" :: Sexp.Atom ":threshold" :: rest) ->
        Common.Refusal.refuse
          "[set-info :threshold] takes exactly one value, got %d"
          (List.length rest)
    | _ -> acc)

(* [from_smt2_file] together with the file's [(set-info :threshold q)], read
   from the same parse (see [threshold_of_sexps]). *)
let from_smt2_file_with_threshold ~print ~inline filename =
  let sexps = read_smt2_sexps filename in
  let threshold = threshold_of_sexps sexps in
  (of_smt2_sexps ~print ~inline sexps, threshold)

(* used for constraints embedded in an OCaml source, where the declared symbols are the
   predicates to infer *)
let from_string ~print ~inline ?(decl_reading = Problem.Synthesize)
    ?(uni_sort = Set.Poly.empty) ?(uni_senv = Map.Poly.empty)
    ?(exi_senv = Map.Poly.empty) ?(dep_map = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) ?(lifted_universals = Map.Poly.empty) =
  Lexing.from_string >> Parser.program Lexer.token
  >> toplevel ~print ~inline []
       {
         decl_reading;
         candidates = Map.Poly.empty;
         lifted_universals;
         uni_sort;
         uni_senv;
         exi_senv;
         dep_map;
         kind_map;
         fenv;
         dtenv;
       }
