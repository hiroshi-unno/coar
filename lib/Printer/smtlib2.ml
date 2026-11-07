open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* Decide on the original environment, before assertion-only preprocessing can
   discard a definition. Unsupported nonempty environments cannot safely use
   Fixedpoint serialization, which omits their defining equations. *)
let has_supported_defining_context fenv =
  if Map.Poly.is_empty fenv then false
  else if Z3Smt.Z3interface.supports_defining_equations fenv then true
  else
    raise
      (PCSP.Problem.NoTemplate
         "the SMT-LIB2 printer cannot preserve this known defining context: \
          supported definitions have Bool/Int signatures, true properties and \
          known calls preserving integer argument positions")

(* The function environment a printed file must account for.  The problem
   builder adds a size function to the environment for every monomorphic
   datatype it is given, as vocabulary for the hypothesis space; the reader
   regenerates it from the datatype declarations the file prints, so a size
   function that no clause and no kept definition applies needs no definition
   in the file and is dropped here.  Recognition is by the complete generated
   entry for a datatype of the problem, never by name, so a user definition
   spelled like a size function stays and is judged as a user definition; and
   a generated entry that a clause or a kept definition does apply stays too,
   since dropping it would print an application of an undefined symbol.
   Without this, every input with a monomorphic datatype -- including the
   printed form of any parametric one, whose instances print as monomorphic
   declarations -- carries a size function over a datatype argument, which the
   defining-context guard does not support, and the printer refuses it. *)
let exported_fenv pcsp =
  let fenv = PCSP.Problem.fenv_of pcsp in
  if Map.Poly.is_empty fenv then fenv
  else
    let generated =
      Map.Poly.data (PCSP.Problem.dtenv_of pcsp)
      |> List.filter ~f:(Fn.non Datatype.is_poly)
      |> List.map ~f:Datatype.size_fun_of
    in
    let is_generated var entry =
      List.exists generated ~f:(fun (var', entry') ->
          Ident.tvar_equal var var'
          &&
          try Poly.equal entry entry'
          with Invalid_argument _ ->
            (* a payload polymorphic equality cannot compare is not shown
               to be the generated entry, so it is kept and judged *)
            false)
    in
    let called syms =
      Set.Poly.filter_map syms ~f:(function
        | FVar (v, _, _) when Map.Poly.mem fenv v -> Some v
        | _ -> None)
    in
    let rec close seen frontier =
      if Set.is_empty frontier then seen
      else
        let seen = Set.union seen frontier in
        let next =
          Set.Poly.union_list
          @@ List.map (Set.to_list frontier) ~f:(fun v ->
                 let _, _, def, _, property = Map.Poly.find_exn fenv v in
                 called
                   (Set.union (Term.funsyms_of def)
                      (Formula.funsyms_of property)))
        in
        close seen (Set.diff next seen)
    in
    let roots =
      Set.union
        (Map.Poly.key_set
           (Map.Poly.filteri fenv ~f:(fun ~key ~data ->
                not (is_generated key data))))
        (Set.Poly.union_list
        @@ List.map ~f:(Formula.funsyms_of >> called)
        @@ Set.to_list
        @@ PCSP.Problem.old_formulas_of pcsp)
    in
    let kept = close Set.Poly.empty roots in
    Map.Poly.filter_keys fenv ~f:(Set.mem kept)

(* Readable sort names for a printed file.  Inside the process a datatype or
   an uninterpreted sort is declared to Z3 under the hex encoding of its
   structural key ([#dt_<hex>], [#sus_<hex>]), which keeps two instances whose
   display names agree (an instance at [Int] and one at an uninterpreted sort
   spelled [int]) apart.  Printed as it is, that name would be read back as the
   name of a nullary datatype, encoded again on the next print, and grow on
   every round trip.  Nothing reads these names back from a printed file except
   a reader, which keys a datatype by the name it reads, so the printer may
   choose them: each encoded name in the text is replaced by a readable name
   decoded from the key -- [Pair], [Lst Int], [Lst (Lst Bool)] -- and where two
   encoded names would print the same, or one would print like a generated
   name, the later in the order of the encoded names gets a [!k] suffix.  The
   replacement is injective over the encoded names of the file and
   deterministic, and a name read back from a printed file prints as itself, so
   printing a printed file is a fixed point.  Constructor and accessor names
   qualified by their datatype ([cons@#dt_<hex>]) are rewritten with it.
   Only identifier atoms are rewritten; literal and comment bytes remain.
   The induced full-symbol mapping must also be injective against user names.
   On collision, a shared fresh marker keeps compound names related while
   making every replacement distinguishable from unchanged source text. *)
let readable_sort_names text =
  let token = Str.regexp "#\\(dt\\|sus\\)_[0-9a-f]+" in
  let slice a b = String.sub text ~pos:a ~len:(b - a) in
  let rec atoms = function
    | Common.Smtlib.Atom (a, b) ->
        let raw = slice a b in
        if String.is_prefix raw ~prefix:"\"" then [] else [ (a, b, raw) ]
    | Common.Smtlib.List (_, _, children) -> List.concat_map children ~f:atoms
  in
  let atoms = List.concat_map (Common.Smtlib.parse text) ~f:atoms in
  let unquote raw =
    if String.is_prefix raw ~prefix:"|" then
      String.sub raw ~pos:1 ~len:(String.length raw - 2)
    else raw
  in
  let tokens =
    let rec collect raw pos acc =
      match Str.search_forward token raw pos with
      | exception Stdlib.Not_found -> acc
      | i ->
          let t = Str.matched_string raw in
          collect raw (i + String.length t) (Set.add acc t)
    in
    Set.to_list
      (List.fold atoms ~init:Set.Poly.empty ~f:(fun acc (_, _, raw) ->
           collect raw 0 acc))
  in
  if List.is_empty tokens then text
  else
    let decode t =
      let hex = List.nth_exn (String.split t ~on:'_') 1 in
      if String.length hex % 2 <> 0 then None
      else
        try
          Some
            (Sexp.of_string
            @@ String.init (String.length hex / 2) ~f:(fun i ->
                   Char.of_int_exn
                   @@ Int.of_string ("0x" ^ String.sub hex ~pos:(2 * i) ~len:2)))
        with _ -> None
    in
    let rec render ~top = function
      | Sexp.List [ Sexp.Atom "int" ] -> "Int"
      | Sexp.List [ Sexp.Atom "bool" ] -> "Bool"
      | Sexp.List [ Sexp.Atom "real" ] -> "Real"
      | Sexp.List [ Sexp.Atom "string" ] -> "String"
      | Sexp.List [ Sexp.Atom "bv"; Sexp.Atom n ] -> sprintf "(_ BitVec %s)" n
      | Sexp.List [ Sexp.Atom "seq"; e ] -> sprintf "(Seq %s)" (render ~top:false e)
      | Sexp.List [ Sexp.Atom "array"; i; e ] ->
          sprintf "(Array %s %s)" (render ~top:false i) (render ~top:false e)
      | Sexp.List
          (Sexp.Atom ("datatype" | "uninterpreted") :: Sexp.Atom name :: params)
        ->
          if List.is_empty params then name
          else
            let body =
              String.concat ~sep:" "
                (name :: List.map params ~f:(render ~top:false))
            in
            if top then body else "(" ^ body ^ ")"
      | sexp -> Sexp.to_string sexp
    in
    let base t =
      let raw =
        match decode t with
        | Some key -> render ~top:true key
        | None -> String.drop_prefix t 1
      in
      (* a quoted symbol cannot hold [|] or [\], and a leading [#] is the
         spelling of a generated name *)
      let raw =
        String.map raw ~f:(function '|' | '\\' -> '_' | c -> c)
      in
      let raw = String.lstrip raw ~drop:(Char.equal '#') in
      if String.is_empty raw then "sort" else raw
    in
    let taken = Hash_set.Poly.create () in
    let names =
      List.map tokens ~f:(fun t ->
          let b = base t in
          let rec pick k =
            let n = if k = 1 then b else sprintf "%s!%d" b k in
            if Hash_set.mem taken n then pick (k + 1) else n
          in
          let n = pick 1 in
          Hash_set.add taken n;
          (t, n))
    in
    let symbols =
      List.map atoms ~f:(fun (_, _, raw) -> unquote raw)
      |> Set.Poly.of_list
    in
    let rewrite table raw =
      Str.global_substitute token
        (fun s -> Map.Poly.find_exn table (Str.matched_string s)) raw
    in
    let table = Map.Poly.of_alist_exn names in
    let table =
      let rewritten = Set.Poly.map symbols ~f:(rewrite table) in
      if Set.length rewritten = Set.length symbols then table
      else
        (* A shared substitution preserves relationships between compound
           names. A fresh marker makes every replacement recoverable and
           avoids capturing any unchanged symbol. *)
        let reserved = Set.to_list symbols @ List.map names ~f:snd in
        let rec fresh prefix =
          if List.exists reserved ~f:(fun name -> String.is_substring name ~substring:prefix)
          then fresh (prefix ^ "!") else prefix
        in
        let prefix = fresh "coar_sort!" in
        List.mapi names ~f:(fun i (token, name) ->
            (token, sprintf "%s%d!%s" prefix i name))
        |> Map.Poly.of_alist_exn
    in
    let renamings =
      Set.to_list symbols
      |> List.filter_map ~f:(fun raw ->
             let renamed = rewrite table raw in
             if String.equal raw renamed then None
             else Some (raw, "|" ^ renamed ^ "|"))
      |> Map.Poly.of_alist_exn
    in
    let buffer = Buffer.create (String.length text) in
    let copied = ref 0 in
    List.iter atoms ~f:(fun (a, b, raw) ->
        Option.iter (Map.Poly.find renamings (unquote raw)) ~f:(fun replacement ->
            Buffer.add_substring buffer text ~pos:!copied ~len:(a - !copied);
            Buffer.add_string buffer replacement;
            copied := b));
    Buffer.add_substring buffer text ~pos:!copied ~len:(String.length text - !copied);
    Buffer.contents buffer

let of_pcsp_plain ~id ?(add_missing_forall = false) (*~print*) pcsp =
  let defining_context = has_supported_defining_context (exported_fenv pcsp) in
  let rec go disambiguate_among =
    let ctx = Z3.mk_context [] in
    let solver = Z3.Fixedpoint.mk_fixedpoint ctx in
    (* print @@ lazy (sprintf "===================== pcsp ====================: \n%s" (PCSP.Problem.str_of pcsp)); *)
    let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
    let dtenv =
      Z3Smt.Z3interface.z3_dtenv_of_dtenv ~disambiguate_among ctx
      @@ PCSP.Problem.dtenv_of pcsp
    in
    let fenv = exported_fenv pcsp in
    let exi_senv = PCSP.Problem.senv_of pcsp in
    (* A predicate KIND is a condition on the solution itself -- a functional
       predicate must be total and single-valued, a well-founded one
       well-founded -- and a constraint format has nowhere to put one.  Written
       as an ordinary [declare-fun ... Bool], the unknown loses that condition,
       and the file is a RELAXATION of the problem it names: every [FN] can be
       [false], which falsifies the premise of every clause mentioning it, so a
       solver reading the file answers [sat] on problems that are [unsat].  So
       every kind is written in the reader's extended syntax, one declaration
       command per kind (the reader's [simple_kind_of_command] and its
       [declare-nwfp] and [declare-parityp] cases are the other half of this
       contract), and the file reads back as the problem it came from.  An
       external solver meets a command it does not know and says so, where the
       plain declaration let it answer a weaker question silently. *)
    let symbol n =
      let plain =
        (not (String.is_empty n))
        && (not (Char.is_digit n.[0]))
        && String.for_all n ~f:(fun c ->
            Char.is_alphanum c || String.mem "~!@$%^&*_-+=<>.?/" c)
      in
      if plain then n else "|" ^ n ^ "|"
    in
    let sort_str s =
      Z3.Sort.to_string
      @@ Z3Smt.Z3interface.of_sort ctx dtenv
      @@ Logic.ExtTerm.to_old_sort s
    in
    (* an NWF family is its shared and per-tag sorts only; the priority fields
       of the record it shares with a parity family are placeholders there.  A
       parity family is the other way round: per-tag sorts and priorities, and
       no shared sorts *)
    let family_str ~parity (nwf : Kind.nwf) =
      let sorts ss = String.concat_map_list ~sep:" " ss ~f:sort_str in
      let trunc =
        let pris = List.init (nwf.max_pri + 3) ~f:Fn.id in
        if List.for_all pris ~f:(fun i -> nwf.trunc i = i) then "identity"
        else if
          List.for_all pris ~f:(fun i ->
              nwf.trunc i = SMT.Smtlib2.halve_truncation i)
        then "halve"
        else
          raise
            (PCSP.Problem.NoTemplate
               (sprintf
                  "the family %s has a truncation that is neither the \
                   identity nor halving, and only those two can be written"
                  (Ident.name_of_tvar nwf.name)))
      in
      let field key body =
        if String.is_empty body then sprintf "(%s)" key
        else sprintf "(%s %s)" key body
      in
      let tags =
        field "tags"
        @@ String.concat_map_list ~sep:" "
           (List.sort ~compare:Stdlib.compare
           @@ Hashtbl.Poly.to_alist nwf.sorts_map)
           ~f:(fun (t, ss) ->
             sprintf "(%s (%s))" (symbol @@ Ident.name_of_tvar t) (sorts ss))
      in
      if not parity then
        sprintf "(%s %s %s)"
          (symbol @@ Ident.name_of_tvar nwf.name)
          (field "shared" @@ sorts nwf.sorts_shared)
          tags
      else if not (List.is_empty nwf.sorts_shared) then
        (* a parity relation relates the disjoint union of its members'
           domains and nothing is shared; every consumer asserts it *)
        raise
          (PCSP.Problem.NoTemplate
             (sprintf "the parity family %s has shared sorts"
                (Ident.name_of_tvar nwf.name)))
      else
      sprintf "(%s %s %s %s %s %s)"
        (symbol @@ Ident.name_of_tvar nwf.name)
        tags
        (field "max-priority" @@ string_of_int nwf.max_pri)
        (field "priority"
        @@ String.concat_map_list ~sep:" " (Map.Poly.to_alist nwf.sigma)
             ~f:(fun (p, i) ->
               sprintf "(%s %d)" (symbol @@ Ident.name_of_tvar p) i))
        (field "accepting"
        @@ String.concat_map_list ~sep:" " (Set.to_list nwf.acc_set)
             ~f:string_of_int)
        (field "truncation" trunc)
    in
    let member cmd nwf (l, r) =
      sprintf "%s %s %s %s" cmd
        (family_str ~parity:(String.equal cmd "declare-parityp") nwf)
        (symbol @@ Ident.name_of_tvar l)
        (symbol @@ Ident.name_of_tvar r)
    in
    let kinded_decls =
      Map.Poly.filter_mapi (PCSP.Problem.kind_map_of pcsp) ~f:(fun ~key ~data ->
          if not (Map.Poly.mem exi_senv key) then None
          else
            match data with
            | Kind.FN -> Some "declare-fnp"
            | Kind.Uniq (j, prov) ->
                Some (sprintf "declare-uniqp %d %s" j (Kind.str_of_provenance prov))
            | Kind.WF -> Some "declare-wfp"
            (* the canonical form for every position set, the empty one
               included; [declare-nep] is read as its alias and never written *)
            | Kind.Tot u ->
                Some
                  (sprintf "declare-totp (%s)"
                     (String.concat_map_list ~sep:" " u ~f:string_of_int))
            | Kind.DWF -> Some "declare-dwfp"
            | Kind.Integ -> Some "declare-integp"
            | Kind.Adm Kind.Adm_expectation -> Some "declare-admp"
            | Kind.Adm Kind.Adm_conditional -> Some "declare-admcp"
            | Kind.Adm Kind.Adm_probability -> Some "declare-admpp"
            | Kind.Adm Kind.Adm_liberal -> Some "declare-admlp"
            | Kind.NWF (nwf, tags) -> Some (member "declare-nwfp" nwf tags)
            | Kind.Parity (nwf, tags) -> Some (member "declare-parityp" nwf tags)
            (* an ordinary predicate needs no command of its own, and a non-Bool
               unknown is refused below with its own reason *)
            | Kind.Ord | Kind.IntFun | Kind.RealFun | Kind.RegEx -> None)
    in
    (* Fixedpoint serialization requires a predicate at a rule's head, even for
       a goal.  Its temporary relation must avoid every user symbol, including
       binders and datatype/function names, not just the unknown declarations.
       The diagnostic form contains those environments and formulas; substring
       exclusion is conservative and terminates on this finite text. *)
    let occupied = PCSP.Problem.str_of pcsp in
    let rec fresh_query name =
      if String.is_substring occupied ~substring:name then fresh_query (name ^ "_")
      else name
    in
    let query_name = fresh_query "__query__" in
    let exi_senv =
      Map.Poly.add_exn exi_senv ~key:(Ident.Tvar query_name)
        ~data:Logic.BoolTerm.SBool
    in
    let penv =
      List.map (Map.Poly.to_alist exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
          let arg_sorts, ret_sort = Logic.Sort.args_ret_of sort in
          if Logic.ExtTerm.is_bool_sort ret_sort then
            let arg_sorts =
              List.map arg_sorts
                ~f:
                  (Logic.ExtTerm.to_old_sort
                  >> Z3Smt.Z3interface.of_sort ctx dtenv)
            in
            let symbol = Z3.Symbol.mk_string ctx name in
            ( Ident.Pvar name,
              Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts
                (Z3.Boolean.mk_sort ctx) )
            (* else if Logic.ExtTerm.is_real_sort ret_sort then (
             assert (List.is_empty arg_sorts);
             let symbol = Z3.Symbol.mk_string ctx name in
             ( Ident.Pvar name,
               Z3.FuncDecl.mk_const_decl ctx symbol
                 (Z3.Arithmetic.Real.mk_sort ctx) )) *)
          else
            (* An unknown whose result sort is not Bool -- what a Horn logic makes of
               `(declare-fun u () Int)`, a FUNCTION to synthesise rather than a relation.
               It cannot be written in this format at all: the output is built through Z3's
               fixedpoint API, which registers RELATIONS, and SMT-LIB2's Horn dialect has no
               syntax for "synthesise this integer" either.  Encoding it as an array-sorted
               universal would change the problem rather than print it, turning an existential
               into a universal.  So this is an unsupported INPUT and is refused as one, by name:
               an assertion here reaches the user as a bare failure naming a file and a line, with
               nothing on the verdict stream, which is a correct refusal wearing the appearance of
               an internal error -- and every harness in this tree reads a non-zero exit with no
               verdict as the tool crashing. *)
            raise
              (PCSP.Problem.NoTemplate
                 (sprintf
                    "the SMT-LIB2 printer writes predicate variables as Z3 \
                     fixedpoint relations, which must return Bool, but the \
                     unknown `%s' returns %s.  An unknown of non-Bool result \
                     sort is a function to synthesise and this format cannot \
                     state one."
                    name
                    (Term.str_of_sort @@ Logic.ExtTerm.to_old_sort ret_sort))))
    in
    List.iter ~f:(snd >> Z3.Fixedpoint.register_relation solver) penv;
    (* one converter for every clause: the recursive functions of [fenv] are
       declared in [ctx] once, which Z3 5.x requires *)
    let export_solver = Z3.Solver.mk_solver ctx None in
    let equations, definitions, of_formula =
      if not defining_context then
        (0, "", Z3Smt.Z3interface.formula_converter ~id ctx penv fenv dtenv)
      else
        (* Fixedpoint serialization omits known definitions, including unused
           contradictory ones. For this supported family, ordinary declarations
           let a Solver serializer collect every dependency without installing
           native recursive definitions. Equations are added first only to make
           the serializer retain those dependencies; replace their assertions
           and declarations with one complete define-funs-rec command below. *)
        let z3fenv =
          Map.Poly.mapi fenv ~f:(fun ~key ~data:(params, sret, _, _, _) ->
              Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar key)
                (List.map params
                   ~f:(snd >> Z3Smt.Z3interface.of_sort ctx dtenv))
                (Z3Smt.Z3interface.of_sort ctx dtenv sret))
        in
        let convert env phi =
          Z3Smt.Z3interface.of_formula_with_z3fenv ~id ctx env penv z3fenv dtenv
            phi
        in
        let equations = Z3Smt.Z3interface.defining_equations_of fenv in
        Z3.Solver.add export_solver (List.map equations ~f:(convert []));
        let name var sort =
          Z3.Expr.to_string
          @@ Z3Smt.Z3interface.of_term ~id ctx [] [] z3fenv dtenv
          @@ Term.mk_var var sort
        in
        let signatures, bodies =
          List.unzip
          @@ List.map (Map.Poly.to_alist fenv)
               ~f:(fun (var, (params, sret, body, _, _)) ->
                 let params =
                   String.concat_map_list ~sep:" " params ~f:(fun (v, s) ->
                       sprintf "(%s %s)" (name v s)
                         (Z3.Sort.to_string
                         @@ Z3Smt.Z3interface.of_sort ctx dtenv s))
                 in
                 let body =
                   if Term.is_let_free body then body else Term.elim_let body
                 in
                 ( sprintf "(%s (%s) %s)"
                     (Z3.Expr.to_string
                     @@ Z3.Expr.mk_const_s ctx (Ident.name_of_tvar var)
                          (Z3Smt.Z3interface.of_sort ctx dtenv sret))
                     params
                     (Z3.Sort.to_string
                     @@ Z3Smt.Z3interface.of_sort ctx dtenv sret),
                   Z3.Expr.to_string
                   @@ Z3Smt.Z3interface.of_term ~id ctx [] penv z3fenv dtenv
                        body ))
        in
        ( List.length equations,
          sprintf "(define-funs-rec (%s) (%s))"
            (String.concat ~sep:" " signatures)
            (String.concat ~sep:" " bodies),
          convert )
    in
    Set.iter (PCSP.Problem.clauses_of pcsp) ~f:(fun (uni_senv, ps, ns, phi) ->
        let senv, phi =
          (* assume that [phi] is alpha-renamed *)
          Formula.elim_let_equivalid
          @@ Normalizer.normalize_let ~rename:true
          @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
        in
        let body =
          Evaluator.simplify @@ Formula.and_of
          @@ Formula.mk_neg phi
             :: (Set.to_list
                @@ Set.Poly.map ~f:Formula.mk_atom
                @@ Set.Poly.map ns
                     ~f:(Logic.ExtTerm.to_old_atm exi_senv uni_senv))
        in

        let head =
          match Set.length ps with
          | 0 ->
              Formula.mk_atom
              @@ Atom.mk_pvar_app (Ident.Pvar query_name) [] []
          | 1 ->
              Formula.or_of @@ Set.to_list
              @@ Set.Poly.map ~f:Formula.mk_atom
              @@ Set.Poly.map ps ~f:(Logic.ExtTerm.to_old_atm exi_senv uni_senv)
          (* Not a solver limitation, though it long read as one: a
             constrained Horn clause has at most one head atom BY DEFINITION of
             the format, so a problem with a disjunctive head has no SMT-LIB2
             Horn form to be written in at all.  Refusing is correct and no
             solver upgrade will change it -- so it is refused as an
             UNSUPPORTED INPUT, by the same route as the non-Bool unknown
             above.  A [failwith] here is indistinguishable from an internal
             error: it escapes as a backtrace with nothing on the verdict
             stream, and a harness reads a non-zero exit with no verdict as
             the tool crashing, which is a correct refusal convicted of the
             one outcome such a check exists to catch. *)
          | _ ->
              raise
                (PCSP.Problem.NoTemplate
                   "a disjunctive head cannot be written as a constrained Horn \
                    clause: the format allows at most one head atom")
        in
        let phi' = Formula.mk_imply body head in
        let senv =
          Map.Poly.to_alist
          @@ Map.force_merge (Logic.to_old_sort_env_map uni_senv) senv
        in
        let c =
          if defining_context then
            of_formula [] (Formula.mk_forall_if_bounded senv phi')
          else of_formula senv phi'
        in
        if defining_context then Z3.Solver.add export_solver [ c ]
        else Z3.Fixedpoint.add_rule solver c None);
    (* set params *)
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params
      (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions")
      false;
    Z3.Fixedpoint.set_parameters solver params;
    (* make smt string *)
    let text =
      (if not defining_context then Z3.Fixedpoint.to_string solver
       else
         let text = Z3.Solver.to_string export_solver in
         let slice a b = String.sub text ~pos:a ~len:(b - a) in
         let remaining = ref equations in
         let declarations, assertions =
           List.partition_map (Common.Smtlib.parse text) ~f:(function
             | Common.Smtlib.List (a, b, Common.Smtlib.Atom (c, d) :: rest) ->
                 if String.equal (slice c d) "assert" then
                   if !remaining > 0 then (
                     decr remaining;
                     Second "")
                   else Second (slice a b)
                 else
                   let known =
                     match (slice c d, rest) with
                     | "declare-fun", Common.Smtlib.Atom (e, f) :: _ ->
                         let token = slice e f in
                         Map.Poly.existsi fenv
                           ~f:(fun ~key ~data:(_, s, _, _, _) ->
                             String.equal token
                               (Z3.Expr.to_string
                               @@ Z3.Expr.mk_const_s ctx
                                    (Ident.name_of_tvar key)
                                    (Z3Smt.Z3interface.of_sort ctx dtenv s)))
                     | _ -> false
                   in
                   First (if known then "" else slice a b)
             | _ -> failwith "unexpected SMT-LIB solver serialization")
         in
         assert (!remaining = 0);
         String.concat ~sep:"\n"
           ([ "(set-logic HORN)" ] @ declarations @ [ definitions ] @ assertions))
    in
    let text =
      if not add_missing_forall then text
      else
        let slice start stop = String.sub text ~pos:start ~len:(stop - start) in
        let bounds = function
          | Common.Smtlib.Atom (a, b) | Common.Smtlib.List (a, b, _) -> (a, b)
        in
        let buffer = Buffer.create (String.length text) in
        let copied = ref 0 in
        List.iter (Common.Smtlib.parse text) ~f:(function
          | Common.Smtlib.List (_, _, [ Common.Smtlib.Atom (a, b); body ])
            when String.equal (slice a b) "assert" ->
              let quantified = match body with
                | Common.Smtlib.List (_, _, Common.Smtlib.Atom (c, d) :: _) ->
                    String.equal (slice c d) "forall"
                | _ -> false
              in
              if not quantified then (
                let start, stop = bounds body in
                Buffer.add_substring buffer text ~pos:!copied ~len:(start - !copied);
                Buffer.add_string buffer "(forall () ";
                Buffer.add_string buffer (slice start stop);
                Buffer.add_char buffer ')';
                copied := stop)
          | _ -> ());
        Buffer.add_substring buffer text ~pos:!copied
          ~len:(String.length text - !copied);
        Buffer.contents buffer
    in
    let inputs =
      String.split_on_chars ~on:[ '\n' ]
      @@ Common.Smtlib.eliminate_query ~name:query_name text
    in
    let inputs = inputs @ [ "(check-sat)" ] in
    (* let inputs = if config.produce_proofs then
      "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
     else inputs in *)
    let inputs = inputs @ [ "(exit)" ] in
    let text = String.concat ~sep:"\n" inputs in
    let text =
      if Map.is_empty kinded_decls then text
      else
        let slice start stop = String.sub text ~pos:start ~len:(stop - start) in
        let command token =
          match SMT.Lexer.token (Lexing.from_string token) with
          | SMT.Parser.ATOM name -> (
              match Map.Poly.find kinded_decls (Ident.Tvar name) with
              | Some _ as command -> command
              | None ->
                  (* Older typed callers may store the raw name that Z3
                     quotes, rather than the reader's retained bars. *)
                  if String.length name >= 2 && Char.equal name.[0] '|'
                     && Char.equal name.[String.length name - 1] '|'
                  then Map.Poly.find kinded_decls
                      (Ident.Tvar (String.sub name ~pos:1
                         ~len:(String.length name - 2)))
                  else None)
          | _ -> None
        in
        let buffer = Buffer.create (String.length text) in
        let copied = ref 0 in
        List.iter (Common.Smtlib.parse text) ~f:(function
          | Common.Smtlib.List (_, _,
              Common.Smtlib.Atom (start, stop)
              :: Common.Smtlib.Atom (name_start, name_stop) :: _)
            when String.equal (slice start stop) "declare-fun" ->
              Option.iter (command (slice name_start name_stop)) ~f:(fun keyword ->
                  Buffer.add_substring buffer text ~pos:!copied ~len:(start - !copied);
                  Buffer.add_string buffer keyword;
                  copied := stop)
          | _ -> ());
        Buffer.add_substring buffer text ~pos:!copied
          ~len:(String.length text - !copied);
        Buffer.contents buffer
    in
    (* Two datatypes can carry constructors of the same name -- one parametric
     datatype instantiated twice gives [int Lst] and [bool Lst], each with
     [nil] -- and a printed file has only the name: [nil] there stands for two
     constructors of two sorts and no reader can tell them apart.  Z3 says
     "ambiguous constant reference ... use a qualified expression
     (as nil <sort>)" and then answers about the assertions it could read.
     Only the file matters, so the check is made on the file: the datatypes it
     actually declares are collected from it, and if two of those spell a
     constructor or accessor the same the problem is printed again with those
     names made distinct.  A file that declares one datatype, or two that do
     not collide, is printed exactly as before.  Every sort a
     [declare-datatypes] command declares is collected, not only its first: a
     mutually recursive group declares several in one command, and a member
     after the first that was left out kept its constructors unqualified in
     two instances of the group, which Z3, cvc5 and this tool's reader all
     reject as ambiguous. *)
    if not (List.is_empty disambiguate_among) then text
    else
      let declared =
        let slice a b = String.sub text ~pos:a ~len:(b - a) in
        (* a sort name is quoted when it contains a space, which an
           instantiated datatype's name does: |int Lst| *)
        let unquote s =
          if String.length s >= 2 && Char.equal s.[0] '|' then
            String.sub s ~pos:1 ~len:(String.length s - 2)
          else s
        in
        List.concat_map (Common.Smtlib.parse text) ~f:(function
          | Common.Smtlib.List
              ( _,
                _,
                Common.Smtlib.Atom (a, b)
                :: Common.Smtlib.List (_, _, sorts)
                :: _ )
            when String.equal (slice a b) "declare-datatypes" ->
              List.filter_map sorts ~f:(function
                | Common.Smtlib.List (_, _, Common.Smtlib.Atom (a, b) :: _) ->
                    Some (unquote (slice a b))
                | _ -> None)
          | _ -> [])
      in
      let collides =
        let dtenv = PCSP.Problem.dtenv_of pcsp in
        let names = Stdlib.Hashtbl.create 32 in
        let dup = ref false in
        List.iter (Map.Poly.data dtenv) ~f:(fun data ->
            List.iter (Datatype.full_dts_of data) ~f:(fun dt ->
                if
                  List.mem declared
                    (Datatype.instance_name (Datatype.update_name data (Datatype.name_of_dt dt)))
                    ~equal:String.equal
                then
                  List.iter (Datatype.conses_of_dt dt) ~f:(fun cons ->
                      let note n =
                        match Stdlib.Hashtbl.find_opt names n with
                        | Some owner
                          when not
                                 (String.equal owner
                                    (Datatype.instance_name (Datatype.update_name data (Datatype.name_of_dt dt)))) ->
                            dup := true
                        | Some _ -> ()
                        | None ->
                            Stdlib.Hashtbl.replace names n
                              (Datatype.instance_name (Datatype.update_name data (Datatype.name_of_dt dt)))
                      in
                      note (Datatype.name_of_cons cons);
                      List.iter (Datatype.sels_of_cons cons) ~f:(function
                          | Datatype.Sel (n, _) | Datatype.InSel (n, _, _) ->
                          note n))));
        !dup
      in
      if collides then go declared else text
  in
  readable_sort_names (go [])

(* A problem that records its universal symbols ([PCSP.Params.dq_universals]),
   written in the reader's dependency-quantified syntax: [DQHORN],
   [declare-forall-sort] for each universal sort, [declare-forall-fun] for
   each universal function, [declare-dep-exists-fun] for each unknown with a
   dependency set, and in every assertion the dependency arguments left
   implicit and the universals named globally.

   The clauses are serialised one assertion each by a Z3 solver, not through
   the fixedpoint API: a problem of this kind may have a clause with a
   disjunctive head (a positive existential skolemised into a functional
   predicate), which no Horn format holds.  In memory each clause has the
   form the reader gives it: an unknown applied to its dependency arguments
   first, a universal function an array-sorted variable bound by the clause's
   own [forall], applied by [select].  In a clause applying an unknown with a
   dependency set, the binders at its leading positions are the universals:
   they leave the binder list, every occurrence is renamed to the universal's
   name, the leading arguments are dropped, and
   [(select ... (select u a1) ... an)] becomes [(u a1 ... an)].  A clause
   applying no such unknown keeps its binders, which is the same clause: a
   universal no unknown depends on is universally quantified there either
   way.  An unknown of kind [FN] is declared [declare-fnp]; any other kind is
   not handled here.

   The record is checked against the text rather than trusted: when an
   application's leading arguments are not the clause's binders, or two
   applications in one clause disagree on them (a preprocessing step changed
   an unknown's arguments), [None] is returned and the caller prints the
   plain form, which is the same problem. *)
type dq_node = A of string | L of dq_node list

exception Dq_mismatch of string

let dq_solver_text ~id pcsp =
  let ctx = Z3.mk_context [] in
  let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
  let dtenv =
    Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp
  in
  let fenv = exported_fenv pcsp in
  if not (Map.Poly.is_empty fenv) then
    raise (Dq_mismatch "a problem with function definitions");
  let exi_senv = PCSP.Problem.senv_of pcsp in
  let penv =
    List.map (Map.Poly.to_alist exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
        let arg_sorts, ret_sort = Logic.Sort.args_ret_of sort in
        if not (Logic.ExtTerm.is_bool_sort ret_sort) then
          raise (Dq_mismatch "an unknown of non-Bool result sort");
        ( Ident.Pvar name,
          Z3.FuncDecl.mk_func_decl ctx
            (Z3.Symbol.mk_string ctx name)
            (List.map arg_sorts
               ~f:(Logic.ExtTerm.to_old_sort >> Z3Smt.Z3interface.of_sort ctx dtenv))
            (Z3.Boolean.mk_sort ctx) ))
  in
  let convert = Z3Smt.Z3interface.formula_converter ~id ctx penv fenv dtenv in
  let solver = Z3.Solver.mk_solver ctx None in
  Set.iter (PCSP.Problem.clauses_of pcsp) ~f:(fun (uni_senv, ps, ns, phi) ->
      let senv, phi =
        Formula.elim_let_equivalid
        @@ Normalizer.normalize_let ~rename:true
        @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
      in
      let atoms s =
        Set.to_list
        @@ Set.Poly.map s ~f:(fun a ->
               Formula.mk_atom (Logic.ExtTerm.to_old_atm exi_senv uni_senv a))
      in
      let body = Formula.and_of (atoms ns) in
      let head = Formula.or_of (phi :: atoms ps) in
      let senv =
        Map.Poly.to_alist
        @@ Map.force_merge (Logic.to_old_sort_env_map uni_senv) senv
      in
      Z3.Solver.add solver
        [ convert [] (Formula.mk_forall_if_bounded senv (Formula.mk_imply body head)) ]);
  readable_sort_names
  @@ Common.Smtlib.strip_annotations
  @@ Z3.Solver.to_string solver

let dq_text_of ~sort_name pcsp text =
  let u = (PCSP.Problem.params_of pcsp).PCSP.Params.dq_universals in
  let kind_map = PCSP.Problem.kind_map_of pcsp in
  let unquote raw =
    if String.length raw >= 2 && Char.equal raw.[0] '|' then
      String.sub raw ~pos:1 ~len:(String.length raw - 2)
    else raw
  in
  let quote n = "|" ^ n ^ "|" in
  let rec of_node = function
    | Common.Smtlib.Atom (a, b) -> A (String.sub text ~pos:a ~len:(b - a))
    | Common.Smtlib.List (_, _, cs) -> L (List.map cs ~f:of_node)
  in
  let rec to_string = function
    | A s -> s
    | L cs -> "(" ^ String.concat_map_list ~sep:" " cs ~f:to_string ^ ")"
  in
  let nodes = List.map (Common.Smtlib.parse text) ~f:of_node in
  (* the serialised uninterpreted sort of each forall-sort, and its name *)
  let sort_map =
    List.map u.forall_sorts ~f:(fun (Ident.Svar n as sv) ->
        (unquote (sort_name (Sort.SVar sv)), quote n))
  in
  let rec rename_sorts = function
    | A s -> (
        match List.Assoc.find sort_map ~equal:String.equal (unquote s) with
        | Some s' -> A s'
        | None -> A s)
    | L cs -> L (List.map cs ~f:rename_sorts)
  in
  let sort_text s = to_string @@ rename_sorts @@ A (sort_name s) in
  let unis =
    List.map u.forall_funs ~f:(fun (x, s) -> (Ident.name_of_tvar x, s))
  in
  (* by the unquoted name: Z3 writes a universal whose name is a simple
     symbol ([!M.f]) without bars *)
  let is_uni f =
    List.exists unis ~f:(fun (x, _) -> String.equal x (unquote f))
  in
  let deps =
    Map.Poly.to_alist u.dep_args
    |> List.map ~f:(fun (p, xs) ->
           (Ident.name_of_tvar p, List.map xs ~f:Ident.name_of_tvar))
  in
  let dep_of name = List.Assoc.find deps ~equal:String.equal (unquote name) in
  let decl_of (x, s) =
    let rec args_ret s =
      if T_array.is_sarray s then
        let a, r = args_ret (T_array.elem_sort_of s) in
        (T_array.index_sort_of s :: a, r)
      else ([], s)
    in
    let args, ret = args_ret s in
    sprintf "(declare-forall-fun %s (%s) %s)" (quote x)
      (String.concat_map_list ~sep:" " args ~f:sort_text)
      (sort_text ret)
  in
  let rec select_to_app = function
    | L [ A "select"; arr; i ] -> (
        match select_to_app arr with
        | A f when is_uni f -> L [ A f; select_to_app i ]
        | L (A f :: args) when is_uni f -> L ((A f :: args) @ [ select_to_app i ])
        | arr' -> L [ A "select"; arr'; select_to_app i ])
    | L cs -> L (List.map cs ~f:select_to_app)
    | a -> a
  in
  let binders_of bs =
    List.map bs ~f:(function
      | L [ A b; s ] -> (b, s)
      | _ -> raise (Dq_mismatch "binder"))
  in
  let clause binders body =
    let ren = Hashtbl.Poly.create () in
    let binder_names = List.map binders ~f:fst in
    let rec scan = function
      | L (A p :: args) when Option.is_some (dep_of p) ->
          let ds = Option.value_exn (dep_of p) in
          let k = List.length ds in
          if List.length args < k then raise (Dq_mismatch "too few arguments");
          List.iter2_exn (List.take args k) ds ~f:(fun a d ->
              match a with
              | A b when List.mem binder_names b ~equal:String.equal -> (
                  match Hashtbl.find ren b with
                  | Some d' when not (String.equal d d') ->
                      raise (Dq_mismatch "one binder, two universals")
                  | _ -> Hashtbl.set ren ~key:b ~data:d)
              | _ -> raise (Dq_mismatch "a dependency argument is not a binder"));
          List.iter (List.drop args k) ~f:scan
      | L cs -> List.iter cs ~f:scan
      | A _ -> ()
    in
    scan body;
    let taken = Hashtbl.data ren in
    if
      List.length (List.dedup_and_sort taken ~compare:String.compare)
      <> List.length taken
    then raise (Dq_mismatch "two binders, one universal");
    let add_bound bound bs =
      List.fold bs ~init:bound ~f:(fun acc -> function
        | L (A b :: _) -> Set.add acc b
        | _ -> acc)
    in
    let rec rewrite bound = function
      | A b when (not (Set.mem bound b)) && Hashtbl.mem ren b ->
          A (quote (Hashtbl.find_exn ren b))
      | L [ (A ("forall" | "exists") as q); L bs; body ] ->
          L [ q; rename_sorts (L bs); rewrite (add_bound bound bs) body ]
      | L [ (A "let" as l); L bs; body ] ->
          let bs' =
            List.map bs ~f:(function
              | L [ A b; t ] -> L [ A b; rewrite bound t ]
              | n -> n)
          in
          L [ l; L bs'; rewrite (add_bound bound bs) body ]
      | L (A p :: args) when Option.is_some (dep_of p) ->
          let k = List.length (Option.value_exn (dep_of p)) in
          L (A p :: List.map (List.drop args k) ~f:(rewrite bound))
      | L cs -> L (List.map cs ~f:(rewrite bound))
      | a -> rename_sorts a
    in
    let binders =
      List.filter binders ~f:(fun (b, _) -> not (Hashtbl.mem ren b))
    in
    let body = select_to_app (rewrite Set.Poly.empty body) in
    if List.is_empty binders then body
    else
      L
        [
          A "forall";
          L (List.map binders ~f:(fun (b, s) -> L [ A b; rename_sorts s ]));
          body;
        ]
  in
  let unknown_decl p sorts ret =
    let kind =
      Map.Poly.find kind_map (Ident.Tvar (unquote p))
      |> Option.value ~default:Kind.Ord
    in
    match (kind, dep_of p) with
    | Kind.Ord, None ->
        to_string (rename_sorts (L [ A "declare-fun"; A p; L sorts; ret ]))
    | Kind.FN, None ->
        to_string (rename_sorts (L [ A "declare-fnp"; A p; L sorts; ret ]))
    | Kind.Ord, Some ds ->
        let k = List.length ds in
        if List.length sorts < k then raise (Dq_mismatch "arity");
        sprintf "(declare-dep-exists-fun %s (%s) %s %s)" p
          (String.concat_map_list ~sep:" " ds ~f:quote)
          (to_string (rename_sorts (L (List.drop sorts k))))
          (to_string ret)
    | _ -> raise (Dq_mismatch "a kind this printer does not write")
  in
  try
    let decls, rest =
      List.partition_map nodes ~f:(function
        | L [ A "declare-sort"; A s; A "0" ]
          when List.Assoc.mem sort_map ~equal:String.equal (unquote s) ->
            First
              (sprintf "(declare-forall-sort %s)"
                 (List.Assoc.find_exn sort_map ~equal:String.equal (unquote s)))
        | L [ A "declare-fun"; A p; L sorts; ret ] ->
            Second (`Unknown (unknown_decl p sorts ret))
        | L [ A "assert"; L [ A "forall"; L bs; body ] ] ->
            Second
              (`Other
                (to_string (L [ A "assert"; clause (binders_of bs) body ])))
        | L [ A "assert"; body ] ->
            Second (`Other (to_string (L [ A "assert"; clause [] body ])))
        | n -> First (to_string (rename_sorts n)))
    in
    let unknowns, asserts =
      List.partition_map rest ~f:(function
        | `Unknown d -> First d
        | `Other a -> Second a)
    in
    Some
      (String.concat ~sep:"\n"
         ([ "(set-logic DQHORN)" ] @ decls
         @ List.map unis ~f:decl_of
         @ unknowns @ asserts @ [ "(check-sat)"; "(exit)" ]))
  with Dq_mismatch _ -> None

(* An SMT problem -- one formula whose free variables are existential --
   written as an SMT-LIB2 script: a declaration per free symbol, the formula
   as one assertion and [(check-sat)], serialised by Z3 from the same
   encoding the solving path gives the formula, so each division keeps its
   rounding mode as that encoding writes it.  A formula applying a function of
   the function environment is refused: its definition is not in the
   formula, and printing the application alone would leave the function
   uninterpreted and the script weaker than the problem.  The refusal is
   [Common.Refusal.Refused], which the entry reports as an unsupported
   input. *)
let of_smt ~id phi =
  let phi =
    Formula.elim_let
    @@ Normalizer.normalize_let ~rename:true
    @@ Typeinf.typeinf_formula ~print:(fun _ -> ())
         ~default:(Some T_int.SInt) phi
  in
  let fenv = get_fenv () in
  if
    Set.exists (Formula.funsyms_of phi) ~f:(function
      | FVar (v, _, _) -> Map.Poly.mem fenv v
      | _ -> false)
  then
    Common.Refusal.refuse
      "the SMT-LIB2 printer does not write the definitions of the functions \
       an SMT problem applies; use smt_format String";
  let ctx = Z3.mk_context [] in
  let dtenv = Z3Smt.Z3interface.z3_dtenv_of_formula ctx phi in
  let solver = Z3.Solver.mk_solver ctx None in
  Z3.Solver.add solver
    [ Z3Smt.Z3interface.of_formula ~id ctx [] [] Map.Poly.empty dtenv phi ];
  readable_sort_names
  @@ Common.Smtlib.strip_annotations
  @@ "(set-logic ALL)\n" ^ Z3.Solver.to_string solver ^ "(check-sat)\n(exit)"

let of_pcsp ~id ?(add_missing_forall = false) pcsp =
  let u = (PCSP.Problem.params_of pcsp).PCSP.Params.dq_universals in
  if PCSP.Params.is_empty_dq_universals u then
    of_pcsp_plain ~id ~add_missing_forall pcsp
  else
    let sort_name s =
      let ctx = Z3.mk_context [] in
      Z3.Sort.to_string
      @@ Z3Smt.Z3interface.of_sort ctx
           (Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (PCSP.Problem.dtenv_of pcsp))
           s
    in
    match
      try dq_text_of ~sort_name pcsp (dq_solver_text ~id pcsp)
      with Dq_mismatch _ -> None
    with
    | Some text -> text
    | None ->
        "; the dependency structure could not be written in the \
         dependency-quantified syntax; the problem is printed with \
         dependencies as ordinary arguments\n"
        ^ of_pcsp_plain ~id ~add_missing_forall pcsp
