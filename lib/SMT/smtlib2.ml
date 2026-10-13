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
  (*| T_int.Abs -> "abs"*)
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
  Fun.protect
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
                   sort mismatch. *)
                failwith
                @@ sprintf
                     "[sort_of_sexp] undeclared sort \"%s\": declare it \
                      (declare-sort/declare-datatypes, or declare-forall-sort \
                      for a sort variable) before its first use"
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
let rec rename_bound_occurrences renaming sexp =
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
            rename_bound_occurrences (without_bound_names params) body;
          ]
    | Sexp.List
        [ Sexp.Atom (("let" | "random") as binder); Sexp.List bindings; body ]
      ->
        let bindings' =
          List.map bindings ~f:(function
            | Sexp.List [ name; rhs ] ->
                Sexp.List [ name; rename_bound_occurrences renaming rhs ]
            | binding -> binding)
        in
        Sexp.List
          [
            Sexp.Atom binder;
            Sexp.List bindings';
            rename_bound_occurrences (without_bound_names bindings) body;
          ]
    | Sexp.List [ Sexp.Atom "as"; identifier; sort ] ->
        Sexp.List
          [ Sexp.Atom "as"; rename_bound_occurrences renaming identifier; sort ]
    | Sexp.List (Sexp.Atom "_" :: _) -> sexp
    | Sexp.List (Sexp.Atom "!" :: term :: attributes) ->
        Sexp.List
          (Sexp.Atom "!" :: rename_bound_occurrences renaming term :: attributes)
    | Sexp.List terms ->
        Sexp.List (List.map terms ~f:(rename_bound_occurrences renaming))

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
    ("to_real", T_irb.mk_int_to_real);
    ("to_int", T_irb.mk_real_to_int);
    ("bv_to_uint", T_irb.mk_bv_to_int ~size:None ~signed:(Some false));
    ("ubv_to_int", T_irb.mk_bv_to_int ~size:None ~signed:(Some false));
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
    ("re.union", (Binary, T_regex.mk_union ~info:Dummy));
    ("re.inter", (Binary, T_regex.mk_inter ~info:Dummy));
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
   of the definition by [lift_universals].  Process-global, written only while a file is read,
   which happens before any solver domain exists; every [define-fun-rec] and [define-funs-rec]
   read sets or removes its names' entries, so an entry never outlives a definition it was
   computed for.

   Why: a universal is universal in every clause, and a clause's universals are renamed,
   quantified and instantiated clause by clause.  A recursive definition is kept in the function
   environment and handed to the SMT solver as one global definition, so a universal left free in
   its body becomes one fixed constant there, unrelated to the clause variable of the same name
   once the clause's variables are renamed or bound: a valid clause relating [f(s[0])] to a
   recursive count over [f] was refuted by a model choosing the constant apart from the clause's
   [f].  Passing the universal as an argument at every application is closure conversion; it
   makes the definition closed and keeps the application's meaning in every model. *)
let lifted_universals : (string, sort_env_list) Hashtbl.t =
  Hashtbl.create (module String)

(* [args] completed with the lifted universals of [name] when it has some and [args] supplies
   exactly the parameters the definition was written with; [args] unchanged otherwise. *)
let with_lifted_args name (fargs : sort_env_list) args =
  match Hashtbl.find lifted_universals name with
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
   [lifted_universals].  Refuses a group in which a member's own parameter is spelled like a
   universal another member mentions free, since the added parameter would collide with it. *)
let lift_universals ~(uni_senv : sort_env_map) group =
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
  if List.is_empty extra then (
    List.iter group ~f:(fun (n, _, _, _) -> Hashtbl.remove lifted_universals n);
    group)
  else (
    List.iter group ~f:(fun (n, (fargs : sort_env_list), _, _) ->
        match
          List.find extra ~f:(fun (x, _) ->
              List.exists fargs ~f:(fst >> Ident.tvar_equal x))
        with
        | Some (x, _) ->
            failwith
            @@ sprintf
                 "[define-fun-rec %s] a parameter is named like the universal %s                   another definition of its group mentions"
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
    List.map group ~f:(fun (n, fargs, sort, body) ->
        Hashtbl.set lifted_universals ~key:n ~data:extra;
        (n, fargs @ extra, sort, close body)))

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
  Fun.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set source_numeric_scope_key saved)
    f

let with_source_numeric_scope ~print (envs : Problem.envs) ~constrs_of
    ~subst_sorts ~map_term f =
  match Stdlib.Domain.DLS.get source_numeric_scope_key with
  | Some _ -> f ()
  | None ->
      let pending = ref Set.Poly.empty in
      Stdlib.Domain.DLS.set source_numeric_scope_key (Some pending);
      Fun.protect
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
              | Some ([], T_bool.SBool, _, true, _) ->
                  (* Recursive placeholders do not contain a formula body.
                     Keep the call symbolic, as in the term and applied paths. *)
                  Formula.of_bool_term
                  @@ Term.mk_fvar_app (Ident.Tvar name) [] T_bool.SBool []
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
              | _ -> failwith @@ sprintf "%s is not bound" name)))
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
      let uni_senv, params = of_random_params ~print ~inline envs params in
      mk_randoms params @@ of_formula ~print ~inline { envs with uni_senv } phi
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
        let mentioned_by_others v =
          List.exists bounds ~f:(fun (v', _, def) ->
              Stdlib.(v' <> v) && Set.mem (Term.tvs_of def) v)
        in
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
          (rename_bound_occurrences (Map.Poly.map renaming ~f:fst) phi)
      in
      List.rev bounds
      |> List.fold ~init:body ~f:(fun body (var, sort, def) ->
          Formula.mk_let_formula (bound_name var) sort def body)
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
                    Formula.subst
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
                  let args = with_lifted_args name fargs args in
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
                  | _ -> failwith @@ sprintf "%s is not bound" name))))
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
  of_formula ~print ~inline { envs with uni_senv }
    (rename_bound_occurrences (Map.Poly.map renaming ~f:fst) phi)

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
          let mentioned_by_others v =
            List.exists def ~f:(fun (v', t) ->
                Stdlib.(v' <> v) && Set.mem (Term.tvs_of t) v)
          in
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
            (rename_bound_occurrences (Map.Poly.map renaming ~f:fst) body)
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
              (rename_bound_occurrences (Map.Poly.singleton x x') body)
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
                match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
                | Some sort -> mk_var (Ident.Tvar name) sort
                | None -> (
                    match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
                    | Some sort -> mk_var (Ident.Tvar name) sort
                    | None -> (
                        match Map.Poly.find envs.fenv (Ident.Tvar name) with
                        | Some ([], sret, t, false, _) ->
                            if inline then t
                            else Term.mk_fvar_app (Ident.Tvar name) [] sret []
                        | Some (fargs, sret, _, true, _)
                          when List.length (with_lifted_args name fargs [])
                               = List.length fargs ->
                            Term.mk_fvar_app (Ident.Tvar name)
                              (List.map ~f:snd fargs) sret
                              (with_lifted_args name fargs [])
                        | Some _ -> failwith ""
                        | None -> (
                            match DTEnv.look_up_func envs.dtenv name with
                            | Some (dt, Datatype.FCons cons)
                              when List.is_empty @@ Datatype.sels_of_cons cons
                              ->
                                (* fresh sort parameters per occurrence, as
                                   [sort_of_sexp] does: two instantiations of
                                   a parametric datatype in one file used to
                                   share the parameters and fail type
                                   inference *)
                                T_dt.mk_cons (Datatype.fresh_of dt) name []
                            | _ -> failwith @@ sprintf "%s is not bound" name)))))))
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
  | Sexp.List
      [ Sexp.List [ Sexp.Atom "_"; Sexp.Atom "int_to_bv"; Sexp.Atom bits ]; t1 ]
    ->
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
            Term.subst sub @@ refresh_binders_term term
          else
            Term.mk_fvar_app (Ident.Tvar name) (List.map ~f:snd fargs) sret
            @@ List.map args ~f:(of_term ~print ~inline envs)
      | Some (fargs, sret, _, true, _) ->
          Term.mk_fvar_app (Ident.Tvar name) (List.map ~f:snd fargs) sret
          @@ with_lifted_args name fargs
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
  List.fold (List.rev sexp) ~init:(envs.uni_senv, [])
    ~f:(fun (uni_senv, params) -> function
    | Sexp.List [ Sexp.Atom name; dist ] ->
        let rand = dist_of_sexp ~print ~inline envs dist in
        ( Map.Poly.add_exn uni_senv ~key:(Ident.Tvar name)
            ~data:(Rand.sort_of rand),
          (Ident.Tvar name, rand) :: params )
    | sexp -> failwith @@ "error of " ^ Sexp.to_string sexp)

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
let definition_scope (envs : Problem.envs) name fargs body =
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
  (fargs, { envs with uni_senv }, rename_bound_occurrences renaming body)

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


let is_available str =
  let logiclist =
    [
      "ALL";
      "HORN";
      "QHORN";
      "DQHORN";
      "SYGUS";
      "QF_LIA";
      "QF_NRA";
      "QF_LIA";
      "QF_LRA";
      "QF_LIRA";
      "QF_NIA";
      "QF_NRA";
      "QF_NIRA";
      "LIA";
      "LRA";
      "NIA";
      "NRA";
      "SAT";
      "QF_DT";
      "QF_UF";
      "QF_BV";
      "BV";
      "QF_ABV";
      "QF_UFBV";
      "QF_AUFBV";
      "QF_ALIA";
      "ALL_SUPPORTED";
      "AUFLIA";
      (* The rest of the logics named on the SMT-LIB site's own logics page.  Every
         name that is not one of HORN/QHORN/DQHORN/SYGUS takes the same branch below
         -- declared symbols are read as uninterpreted, to be interpreted by a model --
         so this list decides nothing but whether the file is read at all, and omitting
         a standard name buys nothing and loses the file.  A file naming a logic this
         reader does not implement in full is still better read and refused later, by
         the operator it actually uses, than refused by its header. *)
      "AUFLIRA";
      "AUFNIRA";
      "UFLRA";
      "UFNIA";
      "QF_AUFLIA";
      "QF_AX";
      "QF_EIA";
      "QF_IDL";
      "QF_RDL";
      "QF_UFIDL";
      "QF_UFLIA";
      "QF_UFLRA";
      "QF_UFNRA";
    ]
  in
  List.exists logiclist ~f:(String.( = ) str)

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
   contains the law's function.  Off by default.  Process-wide, and only ever read while a file
   is being read, which happens before any solver domain exists.

   Why: an unknown that depends on a universal function [f] is, after reading, applied to [f]
   as an argument, so an assertion that applies it speaks of [f] as surely as one that writes
   [f]; but it writes [f] nowhere, so the direct-mention test leaves the law out of it.  The
   clause is then demanded for the unlawful interpretations of [f] as well -- for a loop head
   whose invariant must say [hist_inv(f0, g)], the clause entering the loop asks the invariant to
   hold at [g = f0] for every relation [hist_inv], reflexive or not, which no invariant mentioning
   it can do, and argument filtering then erases [f] from the unknown altogether, since nothing
   constrains it there.  Inserting the premise is sound for the reason given at the [:law]
   expansion: more premises move the expanded problem toward the stated one, never past it. *)
let law_reaches_dependents = ref false

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
   false] turns it off and re-reads the input.  Set, like [law_reaches_dependents], only before a
   file is read.

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

(* add [premise] to an assertion, under its own [forall] when it has one, so that a law written
   with the clause's variable names is instantiated at them rather than nested; with
   [law_dedup_premises], only the conjuncts it does not already assume *)
let assert_with_premise ~names ~premise =
  let mentions = sexp_mentions names in
  fun sexp ->
  if not (mentions sexp) then sexp
  else
    let imply premise phi =
      if not !law_dedup_premises then
        Sexp.List [ Sexp.Atom "=>"; premise; phi ]
      else
        match fresh_premise ~premise phi with
        | None -> phi
        | Some p -> Sexp.List [ Sexp.Atom "=>"; p; phi ]
    in
    match sexp with
    | Sexp.List
        [ Sexp.Atom "assert"; Sexp.List [ Sexp.Atom "forall"; bs; body ] ] ->
        Sexp.List
          [
            Sexp.Atom "assert";
            Sexp.List
              [
                Sexp.Atom "forall";
                bs;
                imply premise body;
              ];
          ]
    | Sexp.List [ Sexp.Atom "assert"; phi ] ->
        Sexp.List [ Sexp.Atom "assert"; imply premise phi ]
    | e -> e

let kind_of_synthesis_target ~fun_sort ~args_sort sret =
  if Term.is_bool_sort sret then Kind.Ord
  else if Term.is_int_sort sret then Kind.IntFun
  else if Term.is_real_sort sret then Kind.RealFun
  else if Term.is_regex_sort sret && List.is_empty args_sort then Kind.RegEx
  else
    failwith
      ("synthesis of a function of the sort " ^ Term.str_of_sort fun_sort
     ^ " is not supported")

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
  | "declare-admp" -> Some (Kind.Adm false)
  | "declare-admcp" -> Some (Kind.Adm true)
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
   introduction check; formal parameters and sort names are separate. *)
let ensure_function_name_fresh ~what (envs : Problem.envs) name =
  let key = Ident.Tvar name in
  if Map.Poly.mem envs.fenv key then
    failwith @@ sprintf "[%s] function %s is already defined" what name;
  if Map.Poly.mem envs.exi_senv key then
    failwith @@ sprintf "[%s] function %s is already declared" what name

(* Aliases and datatype/uninterpreted declarations introduce sort symbols in
   one source namespace. Check the whole group before resolving any bodies;
   local par parameters and term names occupy separate binding contexts. *)
let ensure_sort_names_fresh ~what (envs : Problem.envs) names =
  ignore
  @@ List.fold names ~init:Set.Poly.empty ~f:(fun seen name ->
      if
        Set.mem seen name
        || List.mem theory_sort_names name ~equal:String.equal
        || Hashtbl.mem (sort_aliases ()) name
        || Option.is_some (DTEnv.look_up_dt envs.dtenv name)
        || Set.mem envs.uni_sort (Sort.SVar (Ident.Svar name))
      then failwith @@ sprintf "[%s] sort %s is already declared" what name;
      Set.add seen name)

let ensure_datatype_sort_names_fresh ~what envs declarations =
  ensure_sort_names_fresh ~what envs
  @@ List.map declarations ~f:(function
    | Sexp.List (Sexp.Atom name :: _) -> name
    | sexp ->
        failwith
        @@ sprintf "[%s] invalid datatype declaration: %s" what
             (Sexp.to_string_hum sexp))

let rec toplevel ~print ~inline acc (envs : Problem.envs) = function
  | [] ->
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
        List.map acc
          ~f:
            (Normalizer.normalize_let ~rename:true
            >> Formula.elim_let_with_unknowns synthesis_targets
            >> Normalizer.normalize)
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
      if not (is_available logic) then
        failwith
        @@ sprintf
             "[set-logic] unsupported logic \"%s\" (accepted: see \
              Smtlib2.is_available)"
             logic;
      (* The logic says how a declared symbol is meant, when it says anything at all: a Horn or
         SyGuS problem declares the symbols it wants solved for, an ordinary SMT-LIB logic
         declares symbols a model interprets.  [ALL] and [ALL_SUPPORTED] name no theory
         restriction and are used by both kinds of file, so they leave the caller's choice
         alone. *)
      let envs =
        match logic with
        | "HORN" | "QHORN" | "DQHORN" | "SYGUS" ->
            { envs with Problem.decl_reading = Problem.Synthesize }
        | "ALL" | "ALL_SUPPORTED" -> envs
        | _ -> { envs with Problem.decl_reading = Problem.Uninterpreted }
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
  | Sexp.List (Sexp.Atom "set-info" :: Sexp.Atom name :: t :: _) :: es -> (
      match Map.Poly.find envs.fenv (Tvar name) with
      | Some (fargs, sret, body, is_rec, _ (* ToDo *)) ->
          let fenv =
            (* ToDo *)
            let phi =
              Typeinf.typeinf_formula ~print ~default:None ~to_sus:true
                ~rigid:(rigid_of envs.uni_sort)
              @@ of_formula ~print ~inline envs t
            in
            Map.Poly.set envs.fenv ~key:(Tvar name)
              ~data:(fargs, sret, body, is_rec, phi)
          in
          toplevel ~print ~inline acc { envs with fenv } es
      | None -> toplevel ~print ~inline acc envs es (* ToDo: ignored? *))
  | Sexp.List (Sexp.Atom ("set-info" | "set-option") :: _) :: es
  | Sexp.List [ Sexp.Atom ("get-model" | "check-sat" | "exit") ] :: es
  | Sexp.List (Sexp.Atom "check-sat-using" :: _) :: es ->
      toplevel ~print ~inline acc envs es (* ToDo: ignored? *)
  | Sexp.List [ Sexp.Atom "declare-forall-sort"; Sexp.Atom name ] :: es ->
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
      let names =
        names_reaching
          (name
          ::
          (if !law_reaches_dependents then
             dependents_of
               ~bool_valued:(match ret with Sexp.Atom "Bool" -> true | _ -> false)
               ~synthesize:
                 (match envs.decl_reading with
                 | Problem.Synthesize -> true
                 | Problem.Uninterpreted -> false)
               name es
           else []))
          es
      in
      toplevel ~print ~inline acc envs
        (Sexp.List
           [
             Sexp.Atom "declare-forall-fun"; Sexp.Atom name; Sexp.List args; ret;
           ]
        :: List.map es ~f:(assert_with_premise ~names ~premise:law))
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
        let body = definition_body ~print ~inline body_env sort body in
        Map.Poly.add_exn envs.fenv ~key:(Tvar name)
          ~data:(fargs', sort, body, false, Formula.mk_true ())
      in
      toplevel ~print ~inline acc { envs with fenv = fenv' } es
  | Sexp.List
      [ Sexp.Atom "define-fun-rec"; Sexp.Atom name; Sexp.List fargs; ty; body ]
    :: es ->
      ensure_function_name_fresh ~what:"define-fun-rec" envs name;
      let fenv' =
        let fargs' =
          List.map fargs ~f:(bind_of_sexp ~print envs.uni_sort envs.dtenv)
        in
        let sort = sort_of_sexp ~print envs.uni_sort envs.dtenv None ty in
        let fargs', body_env, body = definition_scope envs name fargs' body in
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
        let fargs', body =
          match
            lift_universals ~uni_senv:envs.uni_senv [ (name, fargs', sort, body) ]
          with
          | [ (_, fargs', _, body) ] -> (fargs', body)
          | _ -> assert false
        in
        Map.Poly.add_exn envs.fenv ~key:(Tvar name)
          ~data:(fargs', sort, body, true, Formula.mk_true ())
      in
      toplevel ~print ~inline acc { envs with fenv = fenv' } es
  | Sexp.List [ Sexp.Atom "assert"; phi ] :: es ->
      toplevel ~print ~inline
        (of_formula ~print ~inline envs phi :: acc)
        envs es
  (* extensions for CHCs *)
  | Sexp.List [ Sexp.Atom "declare-var"; Sexp.Atom name; sort ] :: es ->
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
  (* ordinary SMT-LIB commands.  Those that carry no constraint are
     skipped -- (push)/(pop)/(reset) scopes are not modelled, the file is
     read as one problem; check-sat-assuming's literals become assertions. *)
  | Sexp.List
      (Sexp.Atom
         (( "push" | "pop" | "reset" | "reset-assertions" | "echo" | "get-info"
          | "get-option" | "get-value" | "get-assertions" | "get-assignment"
          | "get-proof" | "get-unsat-core" | "get-unsat-assumptions"
          | "get-objectives" ) as cmd)
      :: _)
    :: es ->
      print @@ lazy (sprintf "[toplevel] (%s ...) ignored" cmd);
      toplevel ~print ~inline acc envs es
  | Sexp.List [ Sexp.Atom "check-sat-assuming"; Sexp.List lits ] :: es ->
      toplevel ~print ~inline acc envs
        (List.map lits ~f:(fun l -> Sexp.List [ Sexp.Atom "assert"; l ]) @ es)
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
            let fargs', envs, body =
              definition_scope { envs with fenv = fenv_placeholders }
                name fargs' body
            in
            let body =
              definition_body ~print ~inline envs sort body
            in
            (name, fargs', sort, body))
      in
      let fenv' =
        List.fold (lift_universals ~uni_senv:envs.uni_senv group)
          ~init:fenv_placeholders ~f:(fun fenv (name, fargs', sort, body) ->
            Map.Poly.set fenv ~key:(Tvar name)
              ~data:(fargs', sort, body, true, Formula.mk_true ()))
      in
      toplevel ~print ~inline acc { envs with fenv = fenv' } es
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
  of_formula ~print ~inline envs phi

let of_term ~print ~inline envs term =
  with_source_numeric_reader_scope @@ fun () -> of_term ~print ~inline envs term

let toplevel ~print ~inline acc envs sexps =
  with_source_numeric_reader_scope @@ fun () ->
  with_sort_alias_scope @@ fun () ->
  List.iter sexps ~f:avoid_generated_names;
  toplevel ~print ~inline acc (seed_builtin_datatypes ~print envs sexps) sexps

(* the plain-SMT entry point: a declared symbol is uninterpreted unless the file's [set-logic]
   asks for synthesis *)
let from_smt2_file ~print ~inline ?(decl_reading = Problem.Uninterpreted)
    ?(uni_sort = Set.Poly.empty) ?(uni_senv = Map.Poly.empty)
    ?(exi_senv = Map.Poly.empty) ?(dep_map = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) filename =
  let sexps =
    In_channel.with_file filename ~f:(fun channel ->
        Parser.program Lexer.token (Lexing.from_channel channel))
  in
  let phis, _envs =
    toplevel ~print ~inline []
      {
        decl_reading;
        candidates = Map.Poly.empty;
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
  let phi = Formula.and_of phis in
  print @@ lazy (sprintf "before typeinf: %s" @@ Formula.str_of phi);
  let phi' =
    Typeinf.typeinf_formula ~print ~default:None ~to_sus:true
      ~rigid:(rigid_of _envs.uni_sort) phi
  in
  print @@ lazy (sprintf "after typeinf: %s" @@ Formula.str_of phi');
  phi'

(* used for constraints embedded in an OCaml source, where the declared symbols are the
   predicates to infer *)
let from_string ~print ~inline ?(decl_reading = Problem.Synthesize)
    ?(uni_sort = Set.Poly.empty) ?(uni_senv = Map.Poly.empty)
    ?(exi_senv = Map.Poly.empty) ?(dep_map = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) =
  Lexing.from_string >> Parser.program Lexer.token
  >> toplevel ~print ~inline []
       {
         decl_reading;
         candidates = Map.Poly.empty;
         uni_sort;
         uni_senv;
         exi_senv;
         dep_map;
         kind_map;
         fenv;
         dtenv;
       }
